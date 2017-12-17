/*
 * Copyright 2010-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.jetbrains.kotlin.backend.konan.optimizations

import org.jetbrains.kotlin.backend.common.IrElementTransformerVoidWithContext
import org.jetbrains.kotlin.backend.common.descriptors.allParameters
import org.jetbrains.kotlin.backend.common.ir.ir2stringWhole
import org.jetbrains.kotlin.backend.common.lower.createIrBuilder
import org.jetbrains.kotlin.backend.konan.Context
import org.jetbrains.kotlin.backend.konan.KonanConfigKeys
import org.jetbrains.kotlin.backend.konan.descriptors.*
import org.jetbrains.kotlin.backend.konan.ir.IrPrivateFunctionCallImpl
import org.jetbrains.kotlin.backend.konan.llvm.*
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.ir.IrElement
import org.jetbrains.kotlin.ir.declarations.*
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.expressions.impl.*
import org.jetbrains.kotlin.ir.visitors.*
import org.jetbrains.kotlin.konan.target.CompilerOutputKind

// TODO: Exceptions, Arrays.

// Devirtualization analysis is performed using Variable Type Analysis algorithm.
// See <TODO: link to the article> for details.
internal object Devirtualization {

    private val DEBUG = 0

    private inline fun DEBUG_OUTPUT(severity: Int, block: () -> Unit) {
        if (DEBUG > severity) block()
    }

    private val TAKE_NAMES = false // Take fqNames for all functions and types (for debug purposes).

    private inline fun takeName(block: () -> String) = if (TAKE_NAMES) block() else null

    private class DevirtualizationAnalysis(val context: Context,
                                           val externalModulesDFG: ExternalModulesDFG,
                                           val moduleDFG: ModuleDFG,
                                           val irModule: IrModuleFragment) {

        private val hasMain = context.config.configuration.get(KonanConfigKeys.PRODUCE) == CompilerOutputKind.PROGRAM

        private val symbolTable = moduleDFG.symbolTable

        class ConstraintGraph {

            private var nodesCount = 0

            val nodes = mutableListOf<Node>()
            val voidNode = Node.Ordinary(nextId(), takeName { "Void" }).also { nodes.add(it) }
            val virtualNode = Node.Source(nextId(), Type.Virtual, takeName { "Virtual" }).also { nodes.add(it) }
            val arrayItemField = DataFlowIR.Field(null, 1, "Array\$Item")
            val functions = mutableMapOf<DataFlowIR.FunctionSymbol, Function>()
            val concreteClasses = mutableMapOf<DataFlowIR.Type.Declared, Node>()
            val externalFunctions = mutableMapOf<DataFlowIR.FunctionSymbol, Node>()
            //val virtualClasses = mutableMapOf<DataFlowIR.Type.Declared, Node>()
            val fields = mutableMapOf<DataFlowIR.Field, Node>() // Do not distinguish receivers.
            val virtualCallSiteReceivers = mutableMapOf<DataFlowIR.Node.VirtualCall, Triple<Node, List<DevirtualizedCallee>, DataFlowIR.FunctionSymbol>>()

            fun nextId(): Int = nodesCount++

            fun addNode(node: Node) = nodes.add(node)

            class Function(val symbol: DataFlowIR.FunctionSymbol, val parameters: Array<Node>, val returns: Node)

//            enum class TypeKind {
//                CONCRETE,
//                VIRTUAL
//            }
//
            data class Type(val type: DataFlowIR.Type.Declared) {
                companion object {
                    fun concrete(type: DataFlowIR.Type.Declared): Type {
                        if (type.isAbstract && type.isFinal)
                            println("ZUGZUG: $type")
                        return if (type.isAbstract) Virtual else Type(type)
                    }

                    fun virtual(type: DataFlowIR.Type.Declared): Type {
                        if (type.isAbstract && type.isFinal)
                            println("ZUGZUG: $type")
                        return if (type.isFinal) Type(type) else Virtual
                    }

                    val Virtual = Type(DataFlowIR.Type.Virtual)
                }
            }

//            data class Type(val type: DataFlowIR.Type.Declared, val kind: TypeKind) {
//                companion object {
//                    fun concrete(type: DataFlowIR.Type.Declared): Type {
//                        if (type.isAbstract && type.isFinal)
//                            println("ZUGZUG: $type")
//                        return Type(type, if (type.isAbstract) TypeKind.VIRTUAL else TypeKind.CONCRETE)
//                    }
//
//                    fun virtual(type: DataFlowIR.Type.Declared): Type {
//                        if (type.isAbstract && type.isFinal)
//                            println("ZUGZUG: $type")
//                        return Type(type, if (type.isFinal) TypeKind.CONCRETE else TypeKind.VIRTUAL)
//                    }
//                }
//            }
//
            sealed class Node(val id: Int) {
                val types = mutableSetOf<Type>()
                val edges = mutableSetOf<Node>()
                val reversedEdges = mutableSetOf<Node>()
                val castEdges = mutableSetOf<CastEdge>()
                val reversedCastEdges = mutableSetOf<CastEdge>()
                var priority = -1

                fun addEdge(node: Node) {
                    edges += node
                    node.reversedEdges += this
                }

                fun addCastEdge(edge: CastEdge) {
                    castEdges += edge
                    edge.node.reversedCastEdges += CastEdge(this, edge.castToType, edge.symbol)
                }

                class Source(id: Int, type: Type, val name: String?): Node(id) {
                    init {
                        types += type
                    }

                    override fun toString(): String {
                        return "Source(name='$name', types='${types.joinToString { it.toString() }}')"
                    }
                }

                class Ordinary(id: Int, val name: String?) : Node(id) {
                    override fun toString(): String {
                        return "Ordinary(name='$name', types='${types.joinToString { it.toString() }}')"
                    }
                }

                data class CastEdge(val node: Node, val castToType: DataFlowIR.Type.Declared, val symbol: DataFlowIR.FunctionSymbol)
            }

            class MultiNode(val nodes: Set<Node>)

            class Condensation(val topologicalOrder: List<MultiNode>)

            private inner class CondensationBuilder {
                private val visited = mutableSetOf<Node>()
                private val order = mutableListOf<Node>()
                private val nodeToMultiNodeMap = mutableMapOf<Node, MultiNode>()
                private val multiNodesOrder = mutableListOf<MultiNode>()

                fun build(): Condensation {
                    // First phase.
                    nodes.forEach {
                        if (!visited.contains(it))
                            findOrder(it)
                    }

                    // Second phase.
                    visited.clear()
                    val multiNodes = mutableListOf<MultiNode>()
                    order.reversed().forEach {
                        if (!visited.contains(it)) {
                            val nodes = mutableSetOf<Node>()
                            paint(it, nodes)
                            multiNodes += MultiNode(nodes)
                        }
                    }

                    // Topsort of built condensation.
                    multiNodes.forEach { multiNode ->
                        multiNode.nodes.forEach { nodeToMultiNodeMap.put(it, multiNode) }
                    }
                    visited.clear()
                    multiNodes.forEach {
                        if (!visited.contains(it.nodes.first()))
                            findMultiNodesOrder(it)
                    }

                    return Condensation(multiNodesOrder)
                }

                private fun findOrder(node: Node) {
                    visited += node
                    node.edges.forEach {
                        if (!visited.contains(it))
                            findOrder(it)
                    }
                    order += node
                }

                private fun paint(node: Node, multiNode: MutableSet<Node>) {
                    visited += node
                    multiNode += node
                    node.reversedEdges.forEach {
                        if (!visited.contains(it))
                            paint(it, multiNode)
                    }
                }

                private fun findMultiNodesOrder(node: MultiNode) {
                    visited.addAll(node.nodes)
                    node.nodes.forEach {
                        it.edges.forEach {
                            if (!visited.contains(it))
                                findMultiNodesOrder(nodeToMultiNodeMap[it]!!)
                        }
                    }
                    multiNodesOrder += node
                }
            }

            fun buildCondensation() = CondensationBuilder().build()
        }

        private val constraintGraph = ConstraintGraph()

        private fun DataFlowIR.Type.resolved(): DataFlowIR.Type.Declared {
            if (this is DataFlowIR.Type.Declared) return this
            val hash = (this as DataFlowIR.Type.External).hash
            return externalModulesDFG.publicTypes[hash] ?: error("Unable to resolve exported type $hash")
        }

        private fun DataFlowIR.FunctionSymbol.resolved(): DataFlowIR.FunctionSymbol {
            if (this is DataFlowIR.FunctionSymbol.External)
                return externalModulesDFG.publicFunctions[this.hash] ?: this
            return this
        }

        private fun DataFlowIR.Type.Declared.isSubtypeOf(other: DataFlowIR.Type.Declared): Boolean {
            return this == other || this.superTypes.any { it.resolved().isSubtypeOf(other) }
        }

        private inner class TypeHierarchy(types: List<DataFlowIR.Type.Declared>) {
            private val typesSubTypes = mutableMapOf<DataFlowIR.Type.Declared, MutableList<DataFlowIR.Type.Declared>>()

            init {
                val visited = mutableSetOf<DataFlowIR.Type.Declared>()

                fun processType(type: DataFlowIR.Type.Declared) {
                    if (type == DataFlowIR.Type.Virtual) return
                    if (!visited.add(type)) return
                    type.superTypes
                            .map { it.resolved() }
                            .forEach { superType ->
                                val subTypes = typesSubTypes.getOrPut(superType, { mutableListOf() })
                                subTypes += type
                                processType(superType)
                            }
                }

                types.forEach { processType(it) }
            }

            private fun findAllInheritors(type: DataFlowIR.Type.Declared, result: MutableSet<DataFlowIR.Type.Declared>) {
                if (!result.add(type)) return
                typesSubTypes[type]?.forEach { findAllInheritors(it, result) }
            }

            fun inheritorsOf(type: DataFlowIR.Type.Declared): List<DataFlowIR.Type.Declared> {
                val result = mutableSetOf<DataFlowIR.Type.Declared>()
                findAllInheritors(type, result)
                return result.toList()
            }
        }

        private inner class InstantiationsSearcher(val moduleDFG: ModuleDFG,
                                                   val externalModulesDFG: ExternalModulesDFG,
                                                   val typeHierarchy: TypeHierarchy) {
            private val visited = mutableSetOf<DataFlowIR.FunctionSymbol>()
            private val typesVirtualCallSites = mutableMapOf<DataFlowIR.Type.Declared, MutableList<DataFlowIR.Node.VirtualCall>>()
            private val instantiatingClasses = mutableSetOf<DataFlowIR.Type.Declared>()

            fun search(): Set<DataFlowIR.Type.Declared> {
                // Rapid Type Analysis: find all instantiations and conservatively estimate call graph.
                instantiatingClasses.clear()

                if (hasMain) {
                    // Optimistic algorithm: traverse call graph from the roots - the entry point and all global initializers.
                    visited.clear()
                    typesVirtualCallSites.clear()

                    dfs(symbolTable.mapFunction(findMainEntryPoint(context)!!))

                    (moduleDFG.functions.values + externalModulesDFG.functionDFGs.values)
                            .filter { it.isGlobalInitializer }
                            .forEach { dfs(it.symbol) }
                } else {
                    moduleDFG.functions.values
                            .filter { it.symbol is DataFlowIR.FunctionSymbol.Public }
                            .forEach {
                                it.parameterTypes
                                        .map { it.resolved() }
                                        .filter { it.isFinal }
                                        .forEach { instantiatingClasses += it }
                            }
                    // For a library assume the worst: find every instantiation and singleton and consider all of them possible.
                    (moduleDFG.functions.values + externalModulesDFG.functionDFGs.values)
                            .asSequence()
                            .flatMap { it.body.nodes.asSequence() }
                            .forEach {
                                when (it) {
                                    is DataFlowIR.Node.NewObject -> instantiatingClasses += it.returnType.resolved()
                                    is DataFlowIR.Node.Singleton -> instantiatingClasses += it.type.resolved()
                                    is DataFlowIR.Node.Const -> instantiatingClasses += it.type.resolved()
                                }
                            }
                }
                return instantiatingClasses
            }

            private fun addInstantiatingClass(type: DataFlowIR.Type) {
                val resolvedType = type.resolved()
                if (!instantiatingClasses.add(resolvedType)) return
                if (DEBUG > 0)
                    println("Adding instantiating class: $resolvedType")
                checkSupertypes(resolvedType, resolvedType, mutableSetOf())
            }

            private fun processVirtualCall(virtualCall: DataFlowIR.Node.VirtualCall,
                                           receiverType: DataFlowIR.Type.Declared) {
                val callee = when (virtualCall) {
                    is DataFlowIR.Node.VtableCall ->
                        receiverType.vtable[virtualCall.calleeVtableIndex]

                    is DataFlowIR.Node.ItableCall -> {
                        if (receiverType.itable[virtualCall.calleeHash] == null) {
                            println("BUGBUGBUG: $receiverType, HASH=${virtualCall.calleeHash}")
                            receiverType.itable.forEach { hash, impl ->
                                println("HASH: $hash, IMPL: $impl")
                            }
                        }
                        receiverType.itable[virtualCall.calleeHash]!!
                    }

                    else -> error("Unreachable")
                }
                dfs(callee)
            }

            private fun checkSupertypes(type: DataFlowIR.Type.Declared,
                                        inheritor: DataFlowIR.Type.Declared,
                                        seenTypes: MutableSet<DataFlowIR.Type.Declared>) {
                seenTypes += type
                typesVirtualCallSites[type]?.toList()?.forEach { processVirtualCall(it, inheritor) }
                typesVirtualCallSites[type]?.let { virtualCallSites ->
                    var index = 0
                    while (index < virtualCallSites.size) {
                        processVirtualCall(virtualCallSites[index], inheritor)
                        ++index
                    }
                }
                type.superTypes
                        .map { it.resolved() }
                        .filterNot { seenTypes.contains(it) }
                        .forEach { checkSupertypes(it, inheritor, seenTypes) }
            }

            private fun dfs(symbol: DataFlowIR.FunctionSymbol) {
                val resolvedFunctionSymbol = symbol.resolved()
                if (resolvedFunctionSymbol is DataFlowIR.FunctionSymbol.External) return
                if (!visited.add(resolvedFunctionSymbol)) return
                if (DEBUG > 0)
                    println("Visiting $resolvedFunctionSymbol")
                val function = (moduleDFG.functions[resolvedFunctionSymbol] ?: externalModulesDFG.functionDFGs[resolvedFunctionSymbol])!!
                nodeLoop@for (node in function.body.nodes) {
                    when (node) {
                        is DataFlowIR.Node.NewObject -> {
                            addInstantiatingClass(node.returnType)
                            dfs(node.callee)
                        }

                        is DataFlowIR.Node.Singleton -> {
                            addInstantiatingClass(node.type)
                            node.constructor?.let { dfs(it) }
                        }

                        is DataFlowIR.Node.Const -> addInstantiatingClass(node.type)

                        is DataFlowIR.Node.StaticCall -> dfs(node.callee)

                        is DataFlowIR.Node.VirtualCall -> {
                            if (node.receiverType == DataFlowIR.Type.Virtual)
                                continue@nodeLoop
                            val receiverType = node.receiverType.resolved()
                            typeHierarchy.inheritorsOf(receiverType)
                                    .filter { instantiatingClasses.contains(it) }
                                    .forEach { processVirtualCall(node, it) }
                            if (DEBUG > 0) {
                                println("Adding virtual callsite:")
                                println("    Receiver: $receiverType")
                                println("    Callee: ${node.callee}")
                                println("    Inheritors:")
                                typeHierarchy.inheritorsOf(receiverType).forEach { println("        $it") }
                            }
                            typesVirtualCallSites.getOrPut(receiverType, { mutableListOf() }).add(node)
                        }
                    }
                }
            }
        }

        fun analyze(): Map<DataFlowIR.Node.VirtualCall, DevirtualizedCallSite> {
            val functions = moduleDFG.functions + externalModulesDFG.functionDFGs
            val typeHierarchy = TypeHierarchy(symbolTable.classMap.values.filterIsInstance<DataFlowIR.Type.Declared>() +
                                              externalModulesDFG.allTypes)
            val instantiatingClasses = InstantiationsSearcher(moduleDFG, externalModulesDFG, typeHierarchy).search()
            val rootSet = getRootSet(irModule)

            val nodesMap = mutableMapOf<DataFlowIR.Node, ConstraintGraph.Node>()
            val variables = mutableMapOf<DataFlowIR.Node.Variable, ConstraintGraph.Node>()
            // TODO: hokum.
            rootSet.filterIsInstance<FunctionDescriptor>()
                    .forEach {
                        val functionSymbol = symbolTable.mapFunction(it).resolved()
                        val function = buildFunctionConstraintGraph(functionSymbol, nodesMap, variables, instantiatingClasses)!!
//                        it.allParameters.forEachIndexed { index, parameter ->
////                            parameter.type.erasure().forEach {
////                                val parameterType = symbolTable.mapClass(it.constructor.declarationDescriptor as ClassDescriptor).resolved()
////                                val node = constraintGraph.virtualClasses.getOrPut(parameterType) {
////                                    ConstraintGraph.Node.Source(constraintGraph.nextId(), "Class\$$parameterType", ConstraintGraph.Type.virtual(parameterType)).also {
////                                        constraintGraph.addNode(it)
////                                    }
////                                }
////                                val node = constraintGraph.virtualNode
////                                node.addEdge(function.parameters[index])
////                            }
//                            val node = constraintGraph.virtualNode
//                            node.addEdge(function.parameters[index])
//                        }
                    }
            functions.values
                    .filter { it.isGlobalInitializer }
                    .forEach {
                        val functionSymbol = it.symbol
                        buildFunctionConstraintGraph(functionSymbol, nodesMap, variables, instantiatingClasses)!!
                        if (DEBUG > 0) {
                            println("CONSTRAINT GRAPH FOR ${functionSymbol}")
                            val function = it
                            val ids = function.body.nodes.withIndex().associateBy({ it.value }, { it.index })
                            for (node in function.body.nodes) {
                                println("FT NODE #${ids[node]}")
                                DataFlowIR.Function.printNode(node, ids)
                                val constraintNode = nodesMap[node] ?: variables[node] ?: break
                                println("       CG NODE #${constraintNode.id}: $constraintNode")
                                println()
                            }
                            println("Returns: #${ids[function.body.returns]}")
                            println()
                        }
                    }

            if (DEBUG > 0) {
                println("FULL CONSTRAINT GRAPH")
                constraintGraph.nodes.forEach {
                    println("    NODE #${it.id}: $it")
                    it.edges.forEach {
                        println("        EDGE: #${it.id}z")
                    }
                    it.types.forEach { println("        TYPE: $it") }
                }
            }
            constraintGraph.nodes.forEach {
                if (it is ConstraintGraph.Node.Source)
                    assert(it.reversedEdges.isEmpty(), { "A source node #${it.id} has incoming edges" })
            }
            println("CONSTRAINT GRAPH: ${constraintGraph.nodes.size} nodes, ${constraintGraph.nodes.sumBy { it.edges.size }} edges")
            val condensation = constraintGraph.buildCondensation()
            val topologicalOrder = condensation.topologicalOrder.reversed()
            if (DEBUG > 0) {
                println("CONDENSATION")
                topologicalOrder.forEachIndexed { index, multiNode ->
                    println("    MULTI-NODE #$index")
                    multiNode.nodes.forEach {
                        println("        #${it.id}: $it")
                    }
                }
            }
            topologicalOrder.forEachIndexed { index, multiNode ->
                multiNode.nodes.forEach { it.priority = index }
            }
            // Handle all 'right-directed' edges.
            // TODO: this is pessimistic handling of Virtual types, think how to do it better.
            topologicalOrder.forEachIndexed { index, multiNode ->
                if (multiNode.nodes.size == 1 && multiNode.nodes.first() is ConstraintGraph.Node.Source)
                    return@forEachIndexed
                val types = mutableSetOf<ConstraintGraph.Type>()
                for (node in multiNode.nodes) {
                    node.reversedEdges.forEach { types += it.types }
                    node.reversedCastEdges
                            .filter { it.node.priority < node.priority }
                            .forEach { (source, castToType) -> types += source.types.filter { it == ConstraintGraph.Type.Virtual || it.type.isSubtypeOf(castToType) } }
                }
                for (node in multiNode.nodes)
                    node.types += types
            }
            val badEdges = mutableListOf<Pair<ConstraintGraph.Node, ConstraintGraph.Node.CastEdge>>()
            for (node in constraintGraph.nodes) {
                node.castEdges
                        .filter { it.node.priority < node.priority } // Contradicts topological order.
                        .forEach { badEdges += node to it }
            }
            badEdges.sortBy { it.second.node.priority } // Heuristic.

            do {
                fun propagateType(node: ConstraintGraph.Node, type: ConstraintGraph.Type) {
                    node.types += type
                    node.edges
                            .filterNot { it.types.contains(type) }
                            .forEach { propagateType(it, type) }
                    node.castEdges
                            .filterNot { it.node.types.contains(type) }
                            .filter { type == ConstraintGraph.Type.Virtual || type.type.isSubtypeOf(it.castToType) }
                            .forEach { propagateType(it.node, type) }
                }

                var end = true
                for ((sourceNode, edge) in badEdges) {
                    val distNode = edge.node
                    sourceNode.types
                            .filter { !distNode.types.contains(it) }
                            .filter { it == ConstraintGraph.Type.Virtual || it.type.isSubtypeOf(edge.castToType) }
                            .forEach {
                                end = false
                                propagateType(distNode, it)
                            }
                }
            } while (!end)
            if (DEBUG > 0) {
                topologicalOrder.forEachIndexed { index, multiNode ->
                    println("Types of multi-node #$index")
                    multiNode.nodes.forEach {
                        println("    Node #${it.id}")
                        it.types.forEach { println("        $it") }
                    }
                }
            }
            val result = mutableMapOf<DataFlowIR.Node.VirtualCall, Pair<DevirtualizedCallSite, DataFlowIR.FunctionSymbol>>()
            val nothing = symbolTable.mapClass(context.builtIns.nothing)
            functions.values
                    .asSequence()
                    .filter { constraintGraph.functions.containsKey(it.symbol) }
                    .flatMap { it.body.nodes.asSequence() }
                    .filterIsInstance<DataFlowIR.Node.VirtualCall>()
                    .forEach { virtualCall ->
                        if (nodesMap[virtualCall] == null) {
                            println("BUGBUGBUG: $virtualCall")
                        }
                        assert (nodesMap[virtualCall] != null, { "Node for virtual call $virtualCall has not been built" })
                        //val callSite = it.callSite ?: return@forEach
                        val receiver = constraintGraph.virtualCallSiteReceivers[virtualCall]
                        if (receiver == null) {
                            result.put(virtualCall, DevirtualizedCallSite(emptyList()) to virtualCall.callee)
                            return@forEach
                        }
                        if (//receiver == null// || receiver.first.types.isEmpty()
                                /*|| */receiver.first.types.any { it == ConstraintGraph.Type.Virtual }) {
                            if (DEBUG > 0) {
                                println("Unable to devirtualize callsite ${virtualCall.callSite?.let { ir2stringWhole(it) } ?: virtualCall.toString() }")
                                //if (receiver == null)
                                  //  println("    receiver = null")
                                //else if (receiver.first.types.isEmpty())
                                  //  println("    no single possible receiver type")
                                //else
                                println("    receiver is Virtual")
                            }
                            return@forEach
                        }
                        val possibleReceivers = receiver.first.types.filterNot { it.type == nothing }
                        val map = receiver.second.associateBy({ it.receiverType }, { it })
                        result.put(virtualCall, DevirtualizedCallSite(possibleReceivers.map {
                            if (map[it.type] == null) {
                                println("BUGBUGBUG: $it, ${it.type.isFinal}, ${it.type.isAbstract}")
                                println(receiver.first)
                                println("Actual receiver types:")
                                possibleReceivers.forEach { println("    $it") }
                                println("Possible receiver types:")
                                map.keys.forEach { println("    $it") }
                            }
                            val devirtualizedCallee = map[it.type]!!
                            val callee = devirtualizedCallee.callee
                            if (callee is DataFlowIR.FunctionSymbol.Declared && callee.symbolTableIndex < 0)
                                error("Function ${devirtualizedCallee.receiverType}.$callee cannot be called virtually," +
                                        " but actually is at call site: ${virtualCall.callSite?.let { ir2stringWhole(it) } ?: virtualCall.toString() }")
//
//                            println("RECEIVER: #${receiver.first.id}")
//                            println("TYPES:")
//                            receiver.first.types.forEach {
//                                println(it)
//                            }

                            devirtualizedCallee
                        }) to receiver.third)
                    }
            if (DEBUG > 0) {
                result.forEach { virtualCall, devirtualizedCallSite ->
                    if (devirtualizedCallSite.first.possibleCallees.isNotEmpty()) {
                        println("DEVIRTUALIZED")
                        println("FUNCTION: ${devirtualizedCallSite.second}")
                        println("CALL SITE: ${virtualCall.callSite?.let { ir2stringWhole(it) } ?: virtualCall.toString()}")
                        println("POSSIBLE RECEIVERS:")
                        devirtualizedCallSite.first.possibleCallees.forEach { println("    TYPE: ${it.receiverType}") }
                        devirtualizedCallSite.first.possibleCallees.forEach { println("    FUN: ${it.callee}") }
                        println()
                    }
                }
            }
            return result.asSequence().associateBy({ it.key }, { it.value.first })
        }

        private fun getRootSet(irModule: IrModuleFragment): Set<CallableDescriptor> {
            val rootSet = mutableSetOf<CallableDescriptor>()
            val hasMain = context.config.configuration.get(KonanConfigKeys.PRODUCE) == CompilerOutputKind.PROGRAM
            if (hasMain)
                rootSet.add(findMainEntryPoint(context)!!)
            irModule.accept(object: IrElementVisitorVoid {
                override fun visitElement(element: IrElement) {
                    element.acceptChildrenVoid(this)
                }

                override fun visitField(declaration: IrField) {
                    declaration.initializer?.let {
                        // Global field.
                        rootSet += declaration.descriptor
                    }
                }

                override fun visitFunction(declaration: IrFunction) {
                    if (!hasMain && declaration.descriptor.isExported()
                            && declaration.descriptor.modality != Modality.ABSTRACT
                            && !declaration.descriptor.externalOrIntrinsic()
                            && declaration.descriptor.kind != CallableMemberDescriptor.Kind.FAKE_OVERRIDE)
                        // For a library take all visible functions.
                        rootSet += declaration.descriptor
                }
            }, data = null)
            return rootSet
        }

        private fun buildFunctionConstraintGraph(symbol: DataFlowIR.FunctionSymbol,
                                                 nodes: MutableMap<DataFlowIR.Node, ConstraintGraph.Node>,
                                                 variables: MutableMap<DataFlowIR.Node.Variable, ConstraintGraph.Node>,
                                                 instantiatingClasses: Collection<DataFlowIR.Type.Declared>)
                : ConstraintGraph.Function? {
            if (symbol is DataFlowIR.FunctionSymbol.External) return null
            constraintGraph.functions[symbol]?.let { return it }

            val function = (moduleDFG.functions[symbol] ?: externalModulesDFG.functionDFGs[symbol])
                    ?: error("Unknown function: $symbol")
            val body = function.body
            val parameters = Array<ConstraintGraph.Node>(symbol.numberOfParameters) {
                ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "Param#$it\$$symbol" }).also {
                    constraintGraph.addNode(it)
                }
            }

            if (!hasMain && symbol is DataFlowIR.FunctionSymbol.Public && moduleDFG.functions.containsKey(symbol)) {
                // Exported function from the current module.
                function.parameterTypes.forEachIndexed { index, type ->
                    if (type.resolved().isFinal) return@forEachIndexed
                    constraintGraph.virtualNode.addEdge(parameters[index])
                }
            }

            val returnsNode = ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "Returns\$$symbol" }).also {
                constraintGraph.addNode(it)
            }
            val functionConstraintGraph = ConstraintGraph.Function(symbol, parameters, returnsNode)
            constraintGraph.functions[symbol] = functionConstraintGraph
            body.nodes.forEach { dfgNodeToConstraintNode(functionConstraintGraph, it, nodes, variables, instantiatingClasses) }
            nodes[body.returns]!!.addEdge(returnsNode)


            if (DEBUG > 0) {
                println("CONSTRAINT GRAPH FOR ${symbol}")
                val ids = function.body.nodes.withIndex().associateBy({ it.value }, { it.index })
                for (node in function.body.nodes) {
                    println("FT NODE #${ids[node]}")
                    DataFlowIR.Function.printNode(node, ids)
                    val constraintNode = nodes[node] ?: variables[node] ?: break
                    println("       CG NODE #${constraintNode.id}: $constraintNode")
                    println()
                }
                println("Returns: #${ids[function.body.returns]}")
                println()
            }

            return functionConstraintGraph
        }

        private fun edgeToConstraintNode(function: ConstraintGraph.Function,
                                         edge: DataFlowIR.Edge,
                                         functionNodesMap: MutableMap<DataFlowIR.Node, ConstraintGraph.Node>,
                                         variables: MutableMap<DataFlowIR.Node.Variable, ConstraintGraph.Node>,
                                         instantiatingClasses: Collection<DataFlowIR.Type.Declared>): ConstraintGraph.Node {
            val result = dfgNodeToConstraintNode(function, edge.node, functionNodesMap, variables, instantiatingClasses)
            val castToType = edge.castToType ?: return result
            val castNode = ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "Cast\$${function.symbol}" })
            constraintGraph.addNode(castNode)
            val castEdge = ConstraintGraph.Node.CastEdge(castNode, castToType.resolved(), function.symbol)
            result.addCastEdge(castEdge)
            return castNode
        }

        /**
         * Takes a function DFG's node and creates a constraint graph node corresponding to it.
         * Also creates all necessary edges.
         */
        private fun dfgNodeToConstraintNode(function: ConstraintGraph.Function,
                                            node: DataFlowIR.Node,
                                            functionNodesMap: MutableMap<DataFlowIR.Node, ConstraintGraph.Node>,
                                            variables: MutableMap<DataFlowIR.Node.Variable, ConstraintGraph.Node>,
                                            instantiatingClasses: Collection<DataFlowIR.Type.Declared>)
                : ConstraintGraph.Node {

            fun edgeToConstraintNode(edge: DataFlowIR.Edge): ConstraintGraph.Node =
                    edgeToConstraintNode(function, edge, functionNodesMap, variables, instantiatingClasses)

            fun argumentToConstraintNode(argument: Any): ConstraintGraph.Node =
                    when (argument) {
                        is ConstraintGraph.Node -> argument
                        is DataFlowIR.Edge -> edgeToConstraintNode(argument)
                        else -> error("Unexpected argument: $argument")
                    }

            fun doCall(callee: ConstraintGraph.Function, arguments: List<Any>): ConstraintGraph.Node {
                assert(callee.parameters.size == arguments.size, { "Function ${callee.symbol} takes ${callee.parameters.size} but caller ${function.symbol} provided ${arguments.size}" })
                callee.parameters.forEachIndexed { index, parameter ->
                    val argument = argumentToConstraintNode(arguments[index])
                    argument.addEdge(parameter)
                }
                return callee.returns
            }

            fun doCall(callee: DataFlowIR.FunctionSymbol,
                       arguments: List<Any>,
                       returnType: DataFlowIR.Type.Declared,
                       receiverType: DataFlowIR.Type.Declared?): ConstraintGraph.Node {
                val resolvedCallee = callee.resolved()
                val calleeConstraintGraph = buildFunctionConstraintGraph(resolvedCallee, functionNodesMap, variables, instantiatingClasses)
                return if (calleeConstraintGraph == null) {
//                    constraintGraph.concreteClasses.getOrPut(returnType) {
//                        ConstraintGraph.Node.Source(constraintGraph.nextId(), ConstraintGraph.Type.concrete(returnType), "Class\$$returnType").also {
//                            constraintGraph.addNode(it)
//                        }
//                    }
//                    constraintGraph.virtualClasses.getOrPut(returnType) {
//                        ConstraintGraph.Node.Source(constraintGraph.nextId(), ConstraintGraph.Type.virtual(returnType), "Class\$$returnType").also {
//                            constraintGraph.addNode(it)
//                        }
//                    }
                    constraintGraph.externalFunctions.getOrPut(resolvedCallee) {
                        val fictitiousReturnNode = ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), "External$resolvedCallee")
                        val possibleReturnTypes = instantiatingClasses.filter { it.isSubtypeOf(returnType) }
                        for (type in possibleReturnTypes) {
                            constraintGraph.concreteClasses.getOrPut(type) {
                                ConstraintGraph.Node.Source(constraintGraph.nextId(), ConstraintGraph.Type.concrete(type), "Class\$$type").also {
                                    constraintGraph.addNode(it)
                                }
                            }.addEdge(fictitiousReturnNode)
                        }
                        fictitiousReturnNode
                    }
                    //constraintGraph.virtualNode
                } else {
                    if (receiverType == null)
                        doCall(calleeConstraintGraph, arguments)
                    else {
                        val receiverNode = argumentToConstraintNode(arguments[0])
                        val castedReceiver = ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "CastedReceiver\$${function.symbol}" })
                        constraintGraph.addNode(castedReceiver)
                        val castedEdge = ConstraintGraph.Node.CastEdge(castedReceiver, receiverType, function.symbol)
                        receiverNode.addCastEdge(castedEdge)
                        doCall(calleeConstraintGraph, listOf(castedReceiver) + arguments.drop(1))
                    }
                }
            }

            if (node is DataFlowIR.Node.Variable && !node.temp) {
                var variableNode = variables[node]
                if (variableNode == null) {
                    variableNode = ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "Variable\$${function.symbol}" }).also {
                        constraintGraph.addNode(it)
                    }
                    variables[node] = variableNode
                    for (value in node.values) {
                        edgeToConstraintNode(value).addEdge(variableNode)
                    }
                }
                return variableNode
            }

            return functionNodesMap.getOrPut(node) {
                when (node) {
                    is DataFlowIR.Node.Const ->
                        ConstraintGraph.Node.Source(constraintGraph.nextId(), ConstraintGraph.Type.concrete(node.type.resolved()), takeName { "Ordinary\$${function.symbol}" }).also {
                            constraintGraph.addNode(it)
                        }

                    is DataFlowIR.Node.Parameter ->
                        function.parameters[node.index]

                    is DataFlowIR.Node.StaticCall ->
                        doCall(node.callee, node.arguments, node.returnType.resolved(), node.receiverType?.resolved())

                    is DataFlowIR.Node.NewObject -> {
                        val returnType = node.returnType.resolved()
                        val instanceNode = constraintGraph.concreteClasses.getOrPut(returnType) {
                            val instanceType = ConstraintGraph.Type.concrete(returnType)
                            ConstraintGraph.Node.Source(constraintGraph.nextId(), instanceType, takeName { "Class\$$returnType" }).also {
                                constraintGraph.addNode(it)
                            }
                        }
                        doCall(node.callee, listOf(instanceNode) + node.arguments, returnType, null)
                        instanceNode
                    }

                    is DataFlowIR.Node.VirtualCall -> {
                        val callee = node.callee
                        if (node.receiverType == DataFlowIR.Type.Virtual)
                            constraintGraph.voidNode
                        else {
                            val receiverType = node.receiverType.resolved()
                            if (DEBUG > 0) {
                                println("Virtual call")
                                println("Caller: ${function.symbol}")
                                println("Callee: $callee")
                                println("Receiver type: $receiverType")
                            }
                            // TODO: optimize by building type hierarchy.
                            val possibleReceiverTypes = instantiatingClasses.filter { it.isSubtypeOf(receiverType) }
                            val callees = possibleReceiverTypes.map {
                                when (node) {
                                    is DataFlowIR.Node.VtableCall ->
                                        it.vtable[node.calleeVtableIndex]

                                    is DataFlowIR.Node.ItableCall -> {
                                        if (it.itable[node.calleeHash] == null) {
                                            println("BUGBUGBUG: $it, HASH=${node.calleeHash}")
                                            it.itable.forEach { hash, impl ->
                                                println("HASH: $hash, IMPL: $impl")
                                            }
                                        }
                                        it.itable[node.calleeHash]!!
                                    }

                                    else -> error("Unreachable")
                                }
                            }
                            if (DEBUG > 0) {
                                println("Possible callees:")
                                callees.forEach { println("$it") }
                                println()
                            }
                            if (callees.isEmpty()) {
                                if (DEBUG > 0) {
                                    println("WARNING: no possible callees for call ${node.callee}")
                                }
                                constraintGraph.voidNode
                            } else {
                                val returnType = node.returnType.resolved()
                                val receiverNode = edgeToConstraintNode(node.arguments[0])
                                val castedReceiver = ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "CastedReceiver\$${function.symbol}" })
                                constraintGraph.addNode(castedReceiver)
                                val castedEdge = ConstraintGraph.Node.CastEdge(castedReceiver, receiverType, function.symbol)
                                receiverNode.addCastEdge(castedEdge)
                                val result = if (callees.size == 1) {
                                    doCall(callees[0], listOf(castedReceiver) + node.arguments.drop(1), returnType, possibleReceiverTypes.single())
                                } else {
                                    val returns = ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "VirtualCallReturns\$${function.symbol}" }).also {
                                        constraintGraph.addNode(it)
                                    }
                                    callees.forEachIndexed { index, actualCallee ->
                                        doCall(actualCallee, listOf(castedReceiver) + node.arguments.drop(1), returnType, possibleReceiverTypes[index]).addEdge(returns)
                                    }
                                    returns
                                }
                                val devirtualizedCallees = possibleReceiverTypes.mapIndexed { index, possibleReceiverType ->
                                    DevirtualizedCallee(possibleReceiverType, callees[index])
                                }
                                constraintGraph.virtualCallSiteReceivers[node] = Triple(castedReceiver, devirtualizedCallees, function.symbol)
                                result
                            }
                        }
                    }

                    is DataFlowIR.Node.Singleton -> {
                        val type = node.type.resolved()
                        node.constructor?.let { buildFunctionConstraintGraph(it, functionNodesMap, variables, instantiatingClasses) }
                        constraintGraph.concreteClasses.getOrPut(type) {
                            ConstraintGraph.Node.Source(constraintGraph.nextId(), ConstraintGraph.Type.concrete(type), takeName { "Class\$$type" }).also {
                                constraintGraph.addNode(it)
                            }
                        }
                    }

                    is DataFlowIR.Node.FieldRead ->
                        constraintGraph.fields.getOrPut(node.field) {
                            ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "Field\$${node.field}" }).also {
                                constraintGraph.addNode(it)
                            }
                        }

                    is DataFlowIR.Node.FieldWrite -> {
                        val fieldNode = constraintGraph.fields.getOrPut(node.field) {
                            ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "Field\$${node.field}" }).also {
                                constraintGraph.addNode(it)
                            }
                        }
                        edgeToConstraintNode(node.value).addEdge(fieldNode)
                        constraintGraph.voidNode
                    }

                    is DataFlowIR.Node.ArrayRead ->
                        constraintGraph.fields.getOrPut(constraintGraph.arrayItemField) {
                            ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "Field\$${constraintGraph.arrayItemField}" }).also {
                                constraintGraph.addNode(it)
                            }
                        }

                    is DataFlowIR.Node.ArrayWrite -> {
                        val fieldNode = constraintGraph.fields.getOrPut(constraintGraph.arrayItemField) {
                            ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "Field\$${constraintGraph.arrayItemField}" }).also {
                                constraintGraph.addNode(it)
                            }
                        }
                        edgeToConstraintNode(node.value).addEdge(fieldNode)
                        constraintGraph.voidNode
                    }

                    is DataFlowIR.Node.Variable ->
                        node.values.map { edgeToConstraintNode(it) }.let { values ->
                            ConstraintGraph.Node.Ordinary(constraintGraph.nextId(), takeName { "TempVar\$${function.symbol}" }).also { node ->
                                constraintGraph.addNode(node)
                                values.forEach { it.addEdge(node) }
                            }
                        }

                    else -> error("Unreachable")
                }
            }
        }
    }

    internal class DevirtualizedCallee(val receiverType: DataFlowIR.Type, val callee: DataFlowIR.FunctionSymbol)

    internal class DevirtualizedCallSite(val possibleCallees: List<DevirtualizedCallee>)

    internal fun analyze(irModule: IrModuleFragment, context: Context,
                         moduleDFG: ModuleDFG, externalModulesDFG: ExternalModulesDFG)
            : Map<DataFlowIR.Node.VirtualCall, DevirtualizedCallSite> {
        return DevirtualizationAnalysis(context, externalModulesDFG, moduleDFG, irModule).analyze()
    }

    internal fun devirtualize(irModule: IrModuleFragment, context: Context,
                              devirtualizedCallSites: Map<IrCall, DevirtualizedCallSite>) {
        irModule.transformChildrenVoid(object: IrElementTransformerVoidWithContext() {
            override fun visitCall(expression: IrCall): IrExpression {
                expression.transformChildrenVoid(this)

                val devirtualizedCallSite = devirtualizedCallSites[expression]
                val actualCallee = devirtualizedCallSite?.possibleCallees?.singleOrNull()?.callee as? DataFlowIR.FunctionSymbol.Declared
                        ?: return expression
                val startOffset = expression.startOffset
                val endOffset = expression.endOffset
                val irBuilder = context.createIrBuilder(currentScope!!.scope.scopeOwnerSymbol, startOffset, endOffset)
                irBuilder.run {
                    val dispatchReceiver = expression.dispatchReceiver!!
                    return IrPrivateFunctionCallImpl(
                            startOffset,
                            endOffset,
                            expression.type,
                            expression.symbol,
                            expression.descriptor,
                            (expression as? IrCallImpl)?.typeArguments,
                            actualCallee.module.descriptor,
                            actualCallee.module.numberOfFunctions,
                            actualCallee.symbolTableIndex
                    ).apply {
                        this.dispatchReceiver    = dispatchReceiver
                        this.extensionReceiver   = expression.extensionReceiver
                        expression.descriptor.valueParameters.forEach {
                            this.putValueArgument(it.index, expression.getValueArgument(it))
                        }
                    }
                }
            }
        })
    }
}
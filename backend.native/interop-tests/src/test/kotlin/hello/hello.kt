interface I {
    fun imeth()
}

interface Bad {
    val x: Int

    fun alloc()
    fun init()
    fun mutableCopy()
}

open class B(var x: Any?) : A() {
    inner class C {
        init {
            println(this@B)
        }
    }

    override fun foo(x: Any?): Any? = x.also { println(x) }
    override fun toString() = "BBB"

    fun println(obj: Any?) = kotlin.io.println(obj)
    fun printAll(objects: List<Any?>) = objects.forEach {
        println(it)
    }

    fun consume(abstractClass: AbstractClass, arg: Any?) {
        abstractClass.abstractMethod(arg)
    }

    fun consume(i: I) = i.imeth()

    fun createI() = object : I {
        override fun imeth() = println("private imeth")
    }

    fun applyTo42(block: ((Long)->Long?)?): Long? = block?.invoke(42)

    val someObjects = listOf(1L, 2L, 3L, null, "Hello", Unit)

    var multBy2 = { x: Int -> x * 2 }

    override public fun any(): Long = 42

    override var propWithPrivateSet
        get() = super.propWithPrivateSet
        public set(value) { super.propWithPrivateSet = value }

    var Any.extensionProperty
        get() = 42
        set(value) = TODO()

}

class KotlinIImpl : I {
    override fun imeth() {}
}

open class A {
    open var propWithPrivateSet: Any = 42
        internal set

    open fun foo(x: Any?): Any? = x
    open fun asIs(value: Any?) = value

    open internal fun any(): Any? = null

    fun printAny() = println(any())
}

fun A.println(obj: Any?) = kotlin.io.println(obj)
val B.x get() = "foobar"

abstract class AbstractClass {
    abstract fun abstractMethod(arg: Any?)
}

data class DC(val x: Int)

fun testAny(x: Any, y: Any) {
    println(x.toString())
    println(x.hashCode())
    println(x == y)
}

var topLevelProperty = 42

//fun main(args: Array<String>) {}

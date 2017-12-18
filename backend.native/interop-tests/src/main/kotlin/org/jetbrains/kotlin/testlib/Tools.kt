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

package org.jetbrains.kotlin.testlib

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.concurrent.TimeUnit

const val PROJECT_DIR = "/Users/ppunegov/ws/kotlin-native/backend.native/interop-tests/"

object CompilerUtils {
    private fun compile(compiler: String, options: List<String>, output: Path) {
        check(Files.notExists(output))
        val executeProcess = ProcessUtils.executeProcess(compiler, *options.toTypedArray())
        assert(executeProcess.exitCode == 0, {
            """Compiler $compiler exited with: ${executeProcess.exitCode}
            |stdout: ${executeProcess.stdOut}
            |stderr: ${executeProcess.stdErr}
            """.trimMargin()
        })
        check(output.toFile().exists(), { "Compiler ${compiler} hasn't produced output file: $output" })
    }

    fun konanc(sources: List<Path>, options: List<String>, output: Path) {
        check(Files.notExists(output))
        val args = sources.map(Path::toString) + options + "-o" + output.toString()
        // TODO use K2Native
        val konanHome = "/Users/ppunegov/ws/kotlin-native/dist"
        val compiler = Paths.get(konanHome, "bin/konanc")
        val executeProcess = ProcessUtils.executeProcess(compiler.toString(), *args.toTypedArray())
        assert(executeProcess.exitCode == 0, {
            """Compiler $compiler exited with: ${executeProcess.exitCode}
            |stdout: ${executeProcess.stdOut}
            |stderr: ${executeProcess.stdErr}
            """.trimMargin()
        })
    }

    fun swiftc(sources: List<Path>, options: List<String>, output: Path) {
        val swiftc = "swiftc"
        val args = options + "-o" + output.toString() + sources.map(Path::toString)
        compile(swiftc, args, output)
    }

    fun clang(sources: List<Path>, options: List<String>, output: Path) {
        // FIXME use Clang from the sysroot by using the project properties: ExecClang, shared?
        val compiler = "clang"
        val args = options + "-o" + output.toString() + sources.map(Path::toString)
        compile(compiler, args, output)
    }
}

object ProcessUtils {
    data class ProcessOutput(val stdOut: String, val stdErr: String, val exitCode: Int)

    fun executeProcess(executable: String, vararg args: String) : ProcessOutput {
        val process = ProcessBuilder(executable, *args).start()
        val out = process.inputStream.bufferedReader().readText()
        val err = process.errorStream.bufferedReader().readText()

        if (!process.waitFor(5L, TimeUnit.MINUTES)) {
            process.destroy()
            error("Process timeout")
        }
        return ProcessOutput(out, err, process.exitValue())
    }
}

fun cleanupOutDir() {
    val outDirPath = Paths.get(PROJECT_DIR, "test-out")
    outDirPath.toFile().deleteRecursively()
    outDirPath.toFile().mkdir()
}

fun compileAndRun(ktl: Path, swift: Path, objc: Path) {
    cleanupOutDir()

    val kotlinSrcName = ktl.fileName.toString().substringBefore(".kt")
    require(kotlinSrcName.isNotEmpty(), { "Incorrect framework name" })
    val framework = kotlinSrcName[0].toUpperCase() + kotlinSrcName.substring(1)

    // Produce framework from Kotlin file
    var options = listOf("-produce", "framework", "-opt")
    var output = Paths.get(PROJECT_DIR, "test-out", framework)
    CompilerUtils.konanc(listOf(ktl), options, output)

    // Compile and run Swift test
    val fwPath = Paths.get(PROJECT_DIR, "test-out").toString()
    options = listOf("-g", "-Xlinker", "-rpath", "-Xlinker", fwPath, "-F", fwPath)
    output = Paths.get(PROJECT_DIR, "test-out/swift.exec")
    CompilerUtils.swiftc(listOf(swift), options, output)

    // TODO: always show compilation output
    // TODO: explain failure

    val result = ProcessUtils.executeProcess(output.toString())
    assert(result.exitCode == 0, {
            "Execution failed with exit code: ${result.exitCode}\n" +
            "stdout/err:\n" + result.stdOut + result.stdErr})
    println(result.stdOut)

    // Compile and run Objective-C test
//    options += listOf("-fobjc-arc", "-framework", framework)
//    output = Paths.get(PROJECT_DIR, "test-out/objc.exec")
//    CompilerUtils.clang(listOf(objc), options, output)
//
//    result = ProcessUtils.executeProcess(output.toString())
//    assert(result.exitCode == 0, { "Execution failed" })
//    println(result.stdOut)
}

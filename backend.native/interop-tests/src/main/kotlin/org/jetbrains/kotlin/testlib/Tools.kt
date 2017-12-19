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

val konanHome = resolveProperty("konan.home")
val testHome = resolveProperty("test.home")
val testOutput = resolveProperty("test.output")

fun resolveProperty(property: String): String {
    return System.getProperty(property) ?: throw RuntimeException("konan.home is not defined")
}

object CompilerUtils {
    private fun compile(compiler: String, options: List<String>, output: Path) {
        check(Files.notExists(output))
        val executeProcess = ProcessUtils.executeProcess(compiler, *options.toTypedArray())
        println("""$compiler finished with exit code: ${executeProcess.exitCode}
            |stdout: ${executeProcess.stdOut}
            |stderr: ${executeProcess.stdErr}
            """.trimMargin())
        check(executeProcess.exitCode == 0, { "Compilation failed" })
    }

    fun konanc(sources: List<Path>, options: List<String>, output: Path) {
        check(Files.notExists(output))
        compile(compiler = Paths.get(konanHome, "bin/konanc").toString(),
                options = sources.map(Path::toString) + options + "-o" + output.toString(),
                output = output)
    }

    fun swiftc(sources: List<Path>, options: List<String>, output: Path) {
        // FIXME: use appropriate swift dependency
        compile(compiler = "swiftc",
                options = options + "-o" + output.toString() + sources.map(Path::toString),
                output = output)
        check(output.toFile().exists(), { "Compiler swift hasn't produced output file: $output" })
    }

    fun clang(sources: List<Path>, options: List<String>, output: Path) {
        // FIXME use Clang from the sysroot by using the project properties: ExecClang
        compile(compiler = "clang",
                options = options + "-o" + output.toString() + sources.map(Path::toString),
                output = output)
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
    val outDirPath = Paths.get(testOutput)
    outDirPath.toFile().deleteRecursively()
    outDirPath.toFile().mkdir()
}

fun compileAndRun(ktl: Path, swift: Path, objc: Path) {
    val kotlinSrcName = ktl.fileName.toString().substringBefore(".kt")
    require(kotlinSrcName.isNotEmpty(), { "Incorrect framework name" })
    val framework = kotlinSrcName[0].toUpperCase() + kotlinSrcName.substring(1)

    // Produce framework from Kotlin file
    var options = listOf("-produce", "framework", "-opt")
    var output = Paths.get(testOutput, framework)
    CompilerUtils.konanc(listOf(ktl), options, output)

    // Compile and run Swift test
    val fwPath = Paths.get(testOutput).toString()
    options = listOf("-g", "-Xlinker", "-rpath", "-Xlinker", fwPath, "-F", fwPath)
    output = Paths.get(testOutput, "swift.exec")
    CompilerUtils.swiftc(listOf(swift), options, output)

    val result = ProcessUtils.executeProcess(output.toString())
    check(result.exitCode == 0, {
            "Execution failed with exit code: ${result.exitCode}\n" +
            "stdout/err:\n" + result.stdOut + result.stdErr})
    println(result.stdOut)
    println(result.stdErr)

    // Compile and run Objective-C test
//    options += listOf("-fobjc-arc", "-framework", framework)
//    output = Paths.get(testHome, "test-out/objc.exec")
//    CompilerUtils.clang(listOf(objc), options, output)
//
//    result = ProcessUtils.executeProcess(output.toString())
//    assert(result.exitCode == 0, { "Execution failed" })
//    println(result.stdOut)
}

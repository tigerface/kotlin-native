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

package hello

import org.jetbrains.kotlin.testlib.*

import org.junit.Test
import org.junit.Before
import java.nio.file.Paths

private const val PROJECT_DIR = "/Users/ppunegov/ws/kotlin-native/backend.native/interop-tests/"

class Test {
    @Before
    fun cleanupOutDir() {
        val outDirPath = Paths.get(PROJECT_DIR, "test-out")
        outDirPath.toFile().deleteRecursively()
        outDirPath.toFile().mkdir()
    }

    @Test
    fun executeSwiftHelp() {
        val result = ProcessUtils.executeProcess("swiftc", "-h")
        assert(result.exitCode == 0)
        println(result.stdOut)
    }

    @Test
    fun compileHello() {
        val swiftSrc = Paths.get(PROJECT_DIR,"/src/test/kotlin/hello/test.swift")
        val ktSrc = Paths.get(PROJECT_DIR, "/src/test/kotlin/hello/hello.kt")
        val objcSrc = Paths.get(PROJECT_DIR,"/src/test/kotlin/hello/test.m")

        compileAndRun(ktSrc, swiftSrc, objcSrc)
    }
}

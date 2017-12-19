package conversions

import org.jetbrains.kotlin.testlib.*
import org.junit.Test

import java.nio.file.Paths

class Test {
    private val testSrcDir = Paths.get(testHome, "test", "kotlin", "conversions")

    @Test
    fun convertValues() {
        val kotlin = testSrcDir.resolve("values.kt")
        val swift = testSrcDir.resolve("values.swift")
        val objc = testSrcDir.resolve("values.m")
        compileAndRun(kotlin, swift, objc)
    }
}
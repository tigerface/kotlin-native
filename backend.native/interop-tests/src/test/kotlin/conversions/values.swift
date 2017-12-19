import Values

// -------- Helpers --------

enum TestError : Error {
    case assertFailed(String)
    case failure
    case testsFailed
}

func assertEquals<T: Equatable>(actual: T, expected: T,
                                 _ message: String = "Assertion failed.") throws {
    if (actual != expected) {
        throw TestError.assertFailed(message + " Expected value: \(expected), but got: \(actual)")
    }
}

func assertEquals<T: Equatable>(actual: [T], expected: [T],
                                 _ message: String = "Assertion failed: arrays not equal") throws {
    try assertEquals(actual: actual.count, expected: expected.count, "Size differs")
    try assertTrue(actual.elementsEqual(expected),
            "Arrays elements are not equal")
}

func assertTrue(_ value: Bool, _ message: String = "Assertion failed.") throws {
    if (value != true) {
        throw TestError.assertFailed(message + " Expected value to be TRUE, but got: \(value)")
    }
}

func assertFalse(_ value: Bool, _ message: String = "Assertion failed.") throws {
    if (value != false) {
        throw TestError.assertFailed(message + " Expected value to be FALSE, but got: \(value)")
    }
}

// -------- Tests --------

func testVals() throws {
    print("Values from Swift")
    let dbl = Values.dbl()
    let flt = Values.flt()
    let int = Values.int()
    let long = Values.long()
    
    print(dbl)
    print(flt)
    print(int)
    print(long)
    
    try assertEquals(actual: dbl, expected: 3.14 as Double, "Double value isn't equal.")
    try assertEquals(actual: flt, expected: 2.73 as Float, "Float value isn't equal.")
    try assertEquals(actual: int, expected: 42)
    try assertEquals(actual: long, expected: 1984)
}

func testVars() throws {
    print("Variables from Swift")
    var intVar = Values.intVar()
    var strVar = Values.str()
    var strAsId = Values.strAsAny()
    
    print(intVar)
    print(strVar)
    print(strAsId)
    
    try assertEquals(actual: intVar, expected: 451)
    try assertEquals(actual: strVar, expected: "Kotlin String")
    try assertEquals(actual: strAsId as! String, expected: "Kotlin String as Any")
    
    strAsId = "Swift str"
    Values.setStrAsAny(strAsId)
    print(Values.strAsAny())
    try assertEquals(actual: Values.strAsAny() as! String, expected: strAsId as! String)
    
    // property with custom getter/setter backed by the Kotlin's var
    var intProp : Int32 {
        get {
            return Values.intVar() * 2
        }
        set(value) {
            Values.setIntVar(123 + value)
        }
    }
    intProp += 10
    print(intProp)
    print(Values.intVar())
    try assertEquals(actual: Values.intVar() * 2, expected: intProp, "Property backed by var")
}

func testDoubles() throws {
    print("Doubles in Swift")
    let minDouble = Values.minDoubleVal()
    let maxDouble = Values.maxDoubleVal()

    print(minDouble)
    print(maxDouble)
    print(Values.nanDoubleVal())
    print(Values.nanFloatVal())
    print(Values.infDoubleVal())
    print(Values.infFloatVal())

    try assertEquals(actual: minDouble, expected: Double.leastNonzeroMagnitude as NSNumber, "Min double")
    try assertEquals(actual: maxDouble, expected: Double.greatestFiniteMagnitude as NSNumber, "Max double")
    try assertTrue(Values.nanDoubleVal().isNaN, "NaN double")
    try assertTrue(Values.nanFloatVal().isNaN, "NaN float")
    try assertEquals(actual: Values.infDoubleVal(), expected: Double.infinity, "Inf double")
    try assertEquals(actual: Values.infFloatVal(), expected: -Float.infinity, "-Inf float")
}

func testLists() throws {
    let numbersList = Values.numbersList()
    let gold = [1, 2.3 as Float, 13.13]
    for i in numbersList {
        print(i)
    }
//    try assertEquals(actual: gold, expected: numbersList as [NSNumber], "Numbers list")

    let anyList = Values.anyList()
    for i in anyList {
        print(i)
    }
//    try assertEquals(actual: gold, expected: anyList, "Numbers list")
}

func testLazyVal() throws {
    let lazyVal = Values.lazyVal()
    print(lazyVal)
    try assertEquals(actual: lazyVal, expected: "Lazily initialized string", "lazy value")
}

let goldenArray = ["Delegated", "global", "array", "property"]

func testDelegatedProp() throws {
    let delegatedGlobalArray = Values.delegatedGlobalArray()
    guard Int(delegatedGlobalArray.size) == goldenArray.count else {
        throw TestError.assertFailed("Size differs")
    }
    for i in 0..<delegatedGlobalArray.size {
        print(delegatedGlobalArray.get(index: i)!)
    }
}

func testGetterDelegate() throws {
    let delegatedList = Values.delegatedList()
    guard delegatedList.count == goldenArray.count else {
        throw TestError.assertFailed("Size differs")
    }
    for val in delegatedList {
        print(val)
    }
}

func testNulls() throws {
    let nilVal : Any? = Values.nullVal()
    try assertTrue(nilVal == nil, "Null value")

    Values.setNullVar(nil)
    var nilVar : Any? = Values.nullVar()
    try assertTrue(nilVar == nil, "Null variable")
}

func testAnyVar() throws {
    var anyVar : Any = Values.anyValue()
    print(anyVar)
    if let str = anyVar as? String {
        print(str)
        try assertEquals(actual: str, expected: "Str")
    } else {
        throw TestError.assertFailed("Incorrect type passed from Any")
    }
}

func testFunctions() throws {
    let _: Any? = Values.emptyFun()

    let str = Values.strFun()
    try assertEquals(actual: str, expected: "fooStr")

    try assertEquals(actual: Values.argsFun(i: 10, l: 20, d: 3.5, s: "res") as! String,
            expected: "res10203.5")
}

func testFuncType() throws {
    let s = "str"
    let fFunc: () -> String = { return s }
    try assertEquals(actual: Values.funArgument(foo: fFunc), expected: s, "Using function type arguments failed")
}

func testGenericsFoo() throws {
    let fun = { (i: Int) -> String in return "S \(i)" }
    // wrap lambda to workaround issue with type conversion inability:
    // (Int) -> String can't be cast to (Any?) -> Any?
    let wrapper = { (t: Any?) -> Any? in return fun(t as! Int) }
    let res = Values.genericFoo(t: 42, foo: wrapper)
    try assertEquals(actual: res as! String, expected: "S 42")
}


//func testVararg() throws {
//    let ktArray = ValuesStdlibArray(size: 3, init: { (_) -> Int in return 42 })
//    let arr: [Int] = Values.varargToList(args: ktArray) as! [Int]
//    try assertEquals(actual: arr, expected: [42, 42, 42])
//}

func testStrExtFun() throws {
    try assertEquals(actual: Values.subExt("String", i: 2), expected: "r")
    try assertEquals(actual: Values.subExt("A", i: 2), expected: "nothing")
}

func testAnyToString() throws {
    try assertEquals(actual: Values.toString(nil), expected: "null")
    try assertEquals(actual: Values.toString(42), expected: "42")
}

func testAnyPrint() throws {
    print("BEGIN")
    Values.print(nil)
    Values.print("Print")
    Values.print(123456789)
    Values.print(3.14)
    Values.print([3, 2, 1])
    print("END")
}

func testLambda() throws {
    try assertEquals(actual: Values.sumLambda()(3, 4), expected: 7)
    // FIXME: fails because Floats passed as NSNumbers while lambda defines parameters as Ints
    // try assertEquals(actual: Values.sumLambda()(3.14, 2.71), expected: 5.85)
}

// -------- Tests for classes and interfaces -------
class ValIEmptyExt : ValuesI {
    func iFun() -> String {
        return "ValIEmptyExt::iFun"
    }
}

class ValIExt : ValuesI {
    func iFun() -> String {
        return "ValIExt::iFun"
    }
}

func testInterfaceExtension() throws {
    try assertEquals(actual: ValIEmptyExt().iFun(), expected: "ValIEmptyExt::iFun")
    try assertEquals(actual: ValIExt().iFun(), expected: "ValIExt::iFun")
}

func testClassInstances() throws {
    try assertEquals(actual: ValuesOpenClassI().iFun(), expected: "OpenClassI::iFun")
    try assertEquals(actual: ValuesDefaultInterfaceExt().iFun(), expected: "I::iFun")
    try assertEquals(actual: ValuesFinalClassExtOpen().iFun(), expected: "FinalClassExtOpen::iFun")
    try assertEquals(actual: ValuesMultiExtClass().iFun(), expected: "PI::iFun")
    try assertEquals(actual: ValuesMultiExtClass().piFun() as! Int, expected: 42)
    try assertEquals(actual: ValuesConstrClass(i: 1, s: "str", a: "Any").iFun(), expected: "OpenClassI::iFun")
    try assertEquals(actual: ValuesExtConstrClass(i: 123).iFun(), expected: "ExtConstrClass::iFun::123-String-AnyS")
}

func testEnum() throws {
    try assertEquals(actual: Values.passEnum().enumValue, expected: 42)
    try assertEquals(actual: Values.passEnum().name, expected: "ANSWER")
    Values.receiveEnum(e: 1)
}

// -------- Execution of the test --------

func main() {
    do {
        try testVals()
        try testVars()
        try testDoubles()
        try testLists()
        try testLazyVal()
        try testDelegatedProp()
        try testGetterDelegate()
        try testNulls()
        try testAnyVar()
        try testFunctions()
        try testFuncType()
        try testGenericsFoo()
//        try testVararg()
        try testStrExtFun()
        try testAnyToString()
        try testAnyPrint()
        try testLambda()

        try testInterfaceExtension()
        try testClassInstances()
        try testEnum()
    } catch {
        print("Tests failed: \(error)")
        abort()
    }
}

autoreleasepool {
    main()
}

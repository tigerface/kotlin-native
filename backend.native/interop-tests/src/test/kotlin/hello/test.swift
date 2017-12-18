import Hello
import Foundation

func main() {
    let b = HelloB(x: nil)
    b.foo(x: b)
    b.x_ = 15
    print(b.description)
    let message: String = "Hello, World!"
    b.println(obj: message)
    b.println(obj: false)
    b.printAll(objects: [false, 1 as Int8, 2 as Int16, ("a" as NSString).character(at: 0), 3 as Int32, 4 as Int64, 5 as Float, 6 as Double, "foo"])
    let applyResult = b.applyTo42 {
        $0 as! Int * 13 as NSNumber
    }
    print(applyResult!)
    print(b.someObjects)
    BSub(x: nil).printAny()
    print(b.x__)

    let dc1 = HelloDC(x: 42)
    let dc2 = HelloDC(x: 42)
    print(dc1.description)
    print(dc1.hash)
    print(dc2.hash)
    print(dc1 == dc2)

    HelloBC(b)
}

class BSub : HelloB {
    override func any() -> Int64 {
        return 17
    }
}

autoreleasepool {
    main()
}


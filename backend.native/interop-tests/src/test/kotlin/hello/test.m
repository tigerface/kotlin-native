#import <Foundation/Foundation.h>
#import <Hello/Hello.h>

@interface AbstractClassImpl : HelloAbstractClass
@end;

@implementation AbstractClassImpl
-(void)abstractMethodArg:(id)arg {
    NSLog(@"abstractMethod: %@", arg);
}
@end;

@interface IImpl : NSObject <HelloI>
@end;
@implementation IImpl
-(void)imeth {
    printf("imeth\n");
}
@end;

@interface DC : NSObject
@end;

@implementation DC
-(NSUInteger)hash {
    return 17;
}
-(BOOL)isEqual:(id)other {
    return true;
}
@end;

int main() {
    @autoreleasepool {
//    NSLog(@"B.class = %@", [B class]);
        HelloB* b = [[HelloB alloc] initWithX:nil];
//    NSLog(@"b = %@", b);
    [b fooX:b];
    [b printlnObj: [NSNumber numberWithBool:YES]];
    [b printlnObj: @"Hello, World!"];
    [b printlnObj_: @888];
    [b printAllObjects: @[@"Hello", @"World", b]];
    AbstractClassImpl* aci = [[AbstractClassImpl alloc] init];
    NSLog(@"aci = %@", aci);
    //[aci abstractMethodArg:@""];
    [b consumeAbstractClass:[[AbstractClassImpl alloc] init] arg:b];
    [b consumeI:[[IImpl alloc] init]];
    NSLog(@"applyTo42 = %@", [b applyTo42Block:^ NSNumber* (NSNumber* arg) {
            NSLog(@"Executing block\n");
            return [NSNumber numberWithLongLong:arg.intValue * 13];
    }]);
    NSLog(@"%@", b);
    NSLog(@"%@", b.someObjects);

    id<HelloI> privateI = [b createI];
    [privateI imeth];
//    NSLog(@"%@", );
    b.x_ = [NSNumber numberWithLong:42];
    NSLog(@"b.x = %@", b.x_);
    NSLog(@"%@", b.multBy2(@((int)42)));
    [Hello testAnyX:[DC new] y:[DC new]];
    }
    return 0;
}

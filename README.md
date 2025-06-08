# zig-cats
A category theory and functional programing library for Zig language.

This library implements some basic data types and functional programming concepts in Haskell, especially the important typeclass in Haskell. Based on Haskell type classes and type combinators, more complex data type construction methods can be implemented. Based on these foundations, we can use the functional programming style to write programs in Zig language, using high-level abstractions to implement complex programs without runtime overhead.

With the help of Zig language's strict type constraints and inference capabilities, type reflection, and compile-time calculations, the use of functional programming style can expose problems as early as possible in the compilation stage, making it easier to reduce errors and write correct programs when designing large and complex programs.

The design and implementation of this library also attempts to explore the boundaries of Zig language's expressiveness and abstraction capabilities. This is a beneficial and bold attempt to combine Zig language with functional programming ideas for good architecture design, which enables the system-level programming language Zig to use some beneficial research results in functional programming.

The library defines type classes such as SemiGroup, Monoid, Functor, Applicative, Monad, and some commonly used data types such as Identity, Constant, AllBool, AnyBool, SumNumb, ProductNumb, Maybe, array, ArrayList, State, etc., and implements instances of the above type classes. In addition, it also implements combinators of some functors, such as Compose, Product, Coproduct. All these type classes support pure data types and impure data types.

## current supported feature list
- [x] SemiGroup
- [x] Monoid

- [x] Functor
- [x] Natural Transformation
- [x] Applicative Functor
- [x] Monad
- [x] Free Monad

- [x] Compose
- [x] Product
- [x] Coproduct

- [ ] Foldable
- [ ] Traversable
- [x] Fixed Point Type
- [x] Catamorphism

## install and integrated to your project
Download and add zig-cats as a dependency by running the following command in your project root:
```bash
zig fetch --save git+https://github.com/flyfish30/zig-cats.git
```
Then add zig-cats as a dependency in your build.zig, add the module to your module as you would normally:
```
    const zig_cats = b.dependency("zig_cats", .{
        .target = target,
        .optimize = optimize,
    });
    exe.root_module.addImport("zig-cats", zig_cats.module("zcats"));
```
Now you can reference types and functions in zig-cats by use @import("zig-cats") in your source code.
```zig
const zcats = @import("zig-cats");

const Functor = zcats.Functor;
const Applicative = zcats.Applicative;
const Monad = zcats.Monad;
const NatTrans = zcats.NatTrans;
```

## build and run or test
The zig-cats is a standard zig project. In this project root directory, you can use bellow command to build it.
```bash
zig build
# add --release=fast to build release version
zig build --release=fast
```
or use bellow command to build and run its sample, this command will check whether the output of sample is correct.
```bash
zig build run
```
Of course, you can run the executable directly by using bellow command:
```bash
zig-out/bin/zcats-sample
```
You can use bellow command to test this project.
```bash
zig build test
```

## use Functor
The zig-cats has implemented some functor instances, you can use them directly through the following zig code:
```zig
    const allocator = testing.allocator;
    const ArrayFunctor = Functor(ArrayList);
    const array_functor = ArrayFunctor.InstanceImpl{ .allocator = allocator };

    var array_a = ArrayList(u32).init(allocator);
    defer array_a.deinit();

    try array_a.appendSlice(&[_]u32{ 0, 1, 2, 3 });
    // The function add10 has been defined in other place.
    array_a = try array_functor.fmap(.InplaceMap, add10, array_a);
    // array_a should be { 10, 11, 12, 13 }

    array_a.clearRetainingCapacity();
    try array_a.appendSlice(&[_]u32{ 10, 20, 30, 40 });
    const array_f64 = try array_functor.fmap(.NewValMap, mul_pi_f64, array_a);
    defer array_f64.deinit();
    // array_a should be { 31.4, 62.8, 94.2, 125.6 }
```
## use Monad
The zig-cats has implemented some monad instances, you can use them directly through the following zig code:
```zig
    const allocator = testing.allocator;
    const ArrayListMonad = Monad(ArrayList);
    const array_monad = ArrayListMonad.InstanceImpl{ .allocator = allocator };
    const ArrayListMImpl = @TypeOf(array_monad);

    var array_a = ArrayList(f64).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]f64{ 10, 20, 30, 40 });
    const array_binded = try array_monad.bind(f64, u32, array_a, struct {
        fn f(impl: *const ArrayListMImpl, a: f64) ArrayListMonad.MbType(u32) {
            var arr_b = try ArrayList(u32).initCapacity(impl.allocator, 2);
            arr_b.appendAssumeCapacity(@intFromFloat(@ceil(a * 4.0)));
            arr_b.appendAssumeCapacity(@intFromFloat(@ceil(a * 9.0)));
            return arr_b;
        }
    }.f);
    defer array_binded.deinit();
    // array_binded should be { 40, 90, 80, 180, 120, 270, 160, 360 }
```

## Examples of zig-cats
The zig-cats library has complete example code that shows the detail usage of zig-cats' Monoid, Functor, Applicative, Monad, etc. 
For details, please refer to https://github.com/flyfish30/zig-cats/tree/main/sample.

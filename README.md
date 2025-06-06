# zig-cats
A category theory and functional programing library for Zig.

zig-cats is a groundbreaking library that masterfully brings core abstractions from Category Theory and Functional Programming into Zig, a language celebrated for its performance, control, and simplicity in systems programming. It achieves this by ingeniously leveraging Zig's powerful comptime capabilities.

These aren't just abstract theories, zig-cats delivers robust, reusable, and typically zero-cost abstract for solving common, practical programming challenges. With zig-cats, Zig developers can unlock new potentials:

* Write more expressive and declarative code.
* Significantly improve code modularity and reusability across different parts of your projects.
* Handle side effects and errors with greater structure and clarity.
* Build complex systems that are easier to reason about, test, and maintain.

zig-cats' explorations push the boundaries of Zig's expressiveness and level of abstraction. It beautifully demonstrates that even in the realm of low-level systems programming, we can elegantly apply profound concepts rooted in mathematics to write code that is both efficient and beautifully structured.

It is implement Monoid, Functor, Applicative, Monad, Compose, Product, Coproduct, etc. All of these are support pure and impure data type.

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
- [ ] Fixed Point Type
- [ ] Catamorphism

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

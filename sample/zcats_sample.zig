const std = @import("std");
const zcats = @import("zcats");
const calc = @import("calc_sample.zig");

const Allocator = std.mem.Allocator;
const Functor = zcats.Functor;
const Applicative = zcats.Applicative;
const Monad = zcats.Monad;
const NatTrans = zcats.NatTrans;

const ComposeApplicative = zcats.ComposeApplicative;
const ProductFG = zcats.ProductFG;
const ProductApplicative = zcats.ProductApplicative;
const CoproductFG = zcats.CoproductFG;
const CoproductApplicative = zcats.CoproductApplicative;

const Maybe = zcats.Maybe;
const MaybeMonadImpl = zcats.MaybeMonadImpl;
const ArrayList = std.ArrayList;
const ArrayListMonadImpl = zcats.ArrayListMonadImpl;
const MaybeToArrayListNatImpl = zcats.MaybeToArrayListNatImpl;

pub fn runZCatsSamples() !void {
    maybeSample();
    try arraylistSample();
    try composeSample();
    try productSample();
    try coproductSample();
    try calc.calcSample();
}

fn maybeSample() void {
    const MaybeMonad = Monad(Maybe);
    var maybe_m = MaybeMonad.InstanceImpl{};

    var maybe_a: ?u32 = 42;
    maybe_a = maybe_m.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 10;
        }
    }.f, maybe_a);

    const maybe_b = maybe_m.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) + 3.14;
        }
    }.f, maybe_a);
    std.debug.print("mapped maybe_a: {any}, maybe_b: {any}\n", .{ maybe_a, maybe_b });

    const maybe_fn: ?*const fn (f64) u32 = struct {
        fn f(x: f64) u32 {
            return @intFromFloat(@floor(x));
        }
    }.f;
    const maybe_applied = maybe_m.fapply(maybe_fn, maybe_b);
    std.debug.print("maybe_applied: {any}\n", .{maybe_applied});
    // The apply function in Maybe can not be null
    // maybe_applied = maybe_m.fapply(null, maybe_applied);
    // std.debug.print("applied with null function: {any}\n", .{maybe_applied});

    const maybe_binded = maybe_m.bind(f64, u32, maybe_b, struct {
        fn f(self: *const MaybeMonadImpl, x: f64) MaybeMonad.MbType(u32) {
            _ = self;
            return @intFromFloat(@ceil(x * 4.0));
        }
    }.f);
    std.debug.print("maybe_binded: {any}\n", .{maybe_binded});
}

fn arraylistSample() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const ArrayListMonad = Monad(ArrayList);
    var array_m = ArrayListMonad.InstanceImpl{ .allocator = allocator };

    var arr = ArrayList(u32).init(allocator);
    defer arr.deinit();
    var i: u32 = 0;
    while (i < 8) : (i += 1) {
        try arr.append(i);
    }

    // example of functor
    arr = try array_m.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 42;
        }
    }.f, arr);
    std.debug.print("arr inplace mapped: {any}\n", .{arr.items});

    const arr_f32 = try array_m.fmap(.InplaceMap, struct {
        fn f(a: u32) f32 {
            return @as(f32, @floatFromInt(a)) + 6.18;
        }
    }.f, arr);
    std.debug.print("arr float32 inplace mapped: {any}\n", .{arr_f32.items});

    arr = try array_m.fmap(.InplaceMap, struct {
        fn f(a: f32) u32 {
            return @as(u32, @intFromFloat(a)) + 58;
        }
    }.f, arr_f32);
    std.debug.print("arr inplace mapped again: {any}\n", .{arr.items});

    const arr_new = try array_m.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) * 3.14;
        }
    }.f, arr);
    defer arr_new.deinit();
    std.debug.print("arr_new: {any}\n", .{arr_new.items});

    // example of applicative functor
    const FloatToIntFn = *const fn (f64) u32;
    const fn_array = [_]FloatToIntFn{
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@floor(x));
            }
        }.f,
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@ceil(x * 4.0));
            }
        }.f,
    };

    var arr_fns = try ArrayList(FloatToIntFn).initCapacity(allocator, fn_array.len);
    defer arr_fns.deinit();
    for (fn_array) |f| {
        arr_fns.appendAssumeCapacity(f);
    }

    const arr_applied = try array_m.fapply(arr_fns, arr_new);
    defer arr_applied.deinit();
    std.debug.print("arr_applied: {any}\n", .{arr_applied.items});

    // example of monad
    const arr_binded = try array_m.bind(f64, u32, arr_new, struct {
        fn f(inst: *const @TypeOf(array_m), a: f64) ArrayListMonad.MbType(u32) {
            var arr_b = try ArrayList(u32).initCapacity(inst.allocator, 2);
            arr_b.appendAssumeCapacity(@intFromFloat(@ceil(a * 4.0)));
            arr_b.appendAssumeCapacity(@intFromFloat(@ceil(a * 9.0)));
            return arr_b;
        }
    }.f);
    defer arr_binded.deinit();
    std.debug.print("arr_binded: {any}\n", .{arr_binded.items});
}

// Deinit the array3 with type ArrayList(Maybe(ArrayList(A))
fn array3Deinit(array3: anytype) void {
    for (array3.items) |item| {
        if (item) |arr| {
            arr.deinit();
        }
    }
    array3.deinit();
}

// pretty print the arr3 with type ArrayList(Maybe(ArrayList(A))
fn array3PrettyPrint(arr3: anytype) void {
    std.debug.print("{{ \n", .{});
    var j: u32 = 0;
    for (arr3.items) |item| {
        if (item) |arr| {
            std.debug.print(" {{ ", .{});
            for (arr.items) |a| {
                std.debug.print("{any},", .{a});
            }
            std.debug.print(" }},", .{});
        } else {
            std.debug.print(" {any},", .{item});
        }

        j += 1;
        if (j == 16) {
            j = 0;
            std.debug.print("\n", .{});
        }
    }
    std.debug.print("}}\n", .{});
}

fn composeSample() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();

    const allocator = gpa.allocator();
    const ArrayListApplicative = Applicative(ArrayList);
    const MaybeApplicative = Applicative(Maybe);
    const ArrayListMaybeApplicative = ComposeApplicative(ArrayListApplicative, MaybeApplicative);

    var array_maybe = ArrayListMaybeApplicative.InstanceImpl{
        .functor_sup = .{
            .instanceF = .{ .allocator = allocator },
            .instanceG = .{},
        },
    };
    var arr = try ArrayList(Maybe(u32)).initCapacity(allocator, 8);
    defer arr.deinit();

    var i: u32 = 8;
    while (i < 8 + 8) : (i += 1) {
        if ((i & 0x1) == 0) {
            arr.appendAssumeCapacity(i);
        } else {
            arr.appendAssumeCapacity(null);
        }
    }

    // example of applicative functor
    arr = try array_maybe.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 42;
        }
    }.f, arr);
    std.debug.print("arr mapped: {any}\n", .{arr.items});

    const arr_new = try array_maybe.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) * 3.14;
        }
    }.f, arr);
    defer arr_new.deinit();
    std.debug.print("arr_new: {any}\n", .{arr_new.items});

    // example of applicative functor
    const FloatToIntFn = *const fn (f64) u32;
    const fn_array = [_]FloatToIntFn{
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@floor(x));
            }
        }.f,
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@ceil(x * 4.0));
            }
        }.f,
    };

    var arr_fns = try ArrayList(Maybe(FloatToIntFn)).initCapacity(allocator, fn_array.len + 1);
    defer arr_fns.deinit();
    for (fn_array) |f| {
        arr_fns.appendAssumeCapacity(f);
    }
    arr_fns.appendAssumeCapacity(null);

    const arr_applied = try array_maybe.fapply(arr_fns, arr_new);
    defer arr_applied.deinit();
    std.debug.print("arr_applied: {any}\n", .{arr_applied.items});

    // example of compose three applicative functor
    const IntToIntFn = *const fn (u32) u32;
    var fn_int_array = [_]IntToIntFn{
        struct {
            fn f(x: u32) u32 {
                return x + 20;
            }
        }.f,
        struct {
            fn f(x: u32) u32 {
                return x * 2;
            }
        }.f,
    };

    const intToFns = struct {
        allocator: Allocator,
        fns: []IntToIntFn,

        const FnSelf = @This();
        pub fn call(self: *const FnSelf, a: u32) Allocator.Error!ArrayList(IntToIntFn) {
            _ = a;
            var arr1_fn = try ArrayList(IntToIntFn).initCapacity(self.allocator, self.fns.len);
            for (self.fns) |f| {
                arr1_fn.appendAssumeCapacity(f);
            }
            return arr1_fn;
        }
    }{ .allocator = allocator, .fns = fn_int_array[0..2] };

    const arr3_fns = try array_maybe.fmapLam(.NewValMap, intToFns, arr);
    defer array3Deinit(arr3_fns);

    const intToArr = struct {
        allocator: Allocator,

        const FnSelf = @This();
        pub fn call(self: *const FnSelf, a: u32) Allocator.Error!ArrayList(u32) {
            var tmp = a;
            var j: u32 = 0;
            var int_arr = try ArrayList(u32).initCapacity(self.allocator, 3);
            while (j < 3) : ({
                j += 1;
                tmp += 2;
            }) {
                int_arr.appendAssumeCapacity(tmp);
            }
            return int_arr;
        }
    }{ .allocator = allocator };

    const arr3_ints = try array_maybe.fmapLam(.NewValMap, intToArr, arr_applied);
    defer array3Deinit(arr3_ints);
    // std.debug.print("arr3_ints: ", .{});
    // array3PrettyPrint(arr3_ints);

    const ArrayMaybeArrayApplicative = ComposeApplicative(ArrayListMaybeApplicative, ArrayListApplicative);
    var array_maybe_array = ArrayMaybeArrayApplicative.InstanceImpl{ .functor_sup = .{
        .instanceF = array_maybe,
        .instanceG = ArrayListApplicative.InstanceImpl{ .allocator = allocator },
    } };

    const arr3_applied = try array_maybe_array.fapply(arr3_fns, arr3_ints);
    defer array3Deinit(arr3_applied);
    std.debug.print("arr3_applied: ", .{});
    array3PrettyPrint(arr3_applied);
}

fn productSample() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();

    const allocator = gpa.allocator();
    const ArrayAndMaybe = ProductFG(ArrayList, Maybe);
    const ArrayListApplicative = Applicative(ArrayList);
    const MaybeApplicative = Applicative(Maybe);
    const ArrayListAndMaybeApplicative = ProductApplicative(ArrayListApplicative, MaybeApplicative);

    var array_and_maybe = ArrayListAndMaybeApplicative.InstanceImpl{
        .functor_sup = .{
            .instanceF = .{ .allocator = allocator },
            .instanceG = .{},
        },
    };

    // pretty print the arr3 with type { ArrayList(A), Maybe(A) }
    const prettyArrayAndMaybe = struct {
        fn prettyPrint(arr_and_maybe: anytype) void {
            std.debug.print("{{ {any}, {any} }}\n", .{ arr_and_maybe[0].items, arr_and_maybe[1] });
        }
    }.prettyPrint;

    var arr = try ArrayList(u32).initCapacity(allocator, 8);
    defer arr.deinit();
    var i: u32 = 8;
    while (i < 8 + 8) : (i += 1) {
        arr.appendAssumeCapacity(i);
    }
    var arr_and_maybe = ArrayAndMaybe(u32){ arr, 42 };

    // example of applicative functor
    arr_and_maybe = try array_and_maybe.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 42;
        }
    }.f, arr_and_maybe);
    std.debug.print("arr_and_maybe mapped: ", .{});
    prettyArrayAndMaybe(arr_and_maybe);

    const arr_and_maybe_new = try array_and_maybe.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) * 3.14;
        }
    }.f, arr_and_maybe);
    defer arr_and_maybe_new[0].deinit();
    std.debug.print("arr_and_maybe_new: ", .{});
    prettyArrayAndMaybe(arr_and_maybe_new);

    // example of applicative functor
    const FloatToIntFn = *const fn (f64) u32;
    const fn_array = [_]FloatToIntFn{
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@floor(x));
            }
        }.f,
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@ceil(x * 4.0));
            }
        }.f,
    };

    var arr_fns = try ArrayList(FloatToIntFn).initCapacity(allocator, fn_array.len);
    defer arr_fns.deinit();
    for (fn_array) |f| {
        arr_fns.appendAssumeCapacity(f);
    }
    const arr_and_maybe_fns = ArrayAndMaybe(FloatToIntFn){ arr_fns, fn_array[0] };

    const arr_and_maybe_applied = try array_and_maybe.fapply(arr_and_maybe_fns, arr_and_maybe_new);
    defer arr_and_maybe_applied[0].deinit();
    std.debug.print("arr_and_maybe_applied: ", .{});
    prettyArrayAndMaybe(arr_and_maybe_applied);
}

fn coproductSample() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();

    const allocator = gpa.allocator();
    const ArrayOrMaybe = CoproductFG(ArrayList, Maybe);
    const ArrayListApplicative = Applicative(ArrayList);
    const MaybeApplicative = Applicative(Maybe);
    const NatMaybeToArray = NatTrans(MaybeToArrayListNatImpl);
    const ArrayListOrMaybeApplicative = CoproductApplicative(
        ArrayListApplicative,
        MaybeApplicative,
        NatMaybeToArray,
    );

    var array_or_maybe = ArrayListOrMaybeApplicative.InstanceImpl{
        .functor_sup = .{
            // ArrayList Applicative instance
            .instanceF = .{ .allocator = allocator },
            // Maybe Applicative instance
            .instanceG = .{},
        },
        // NatMaybeToArrayList Applicative instance
        .natural_gf = .{ .instanceArray = .{ .allocator = allocator } },
    };

    // pretty print the arr_or_maybe with type Coproduct(ArrayList, Maybe)
    const prettyArrayOrMaybe = struct {
        fn prettyPrint(arr_or_maybe: anytype) void {
            if (arr_or_maybe == .inl) {
                std.debug.print("{{ inl: {any} }}\n", .{arr_or_maybe.inl.items});
            } else {
                std.debug.print("{{ inr: {any} }}\n", .{arr_or_maybe.inr});
            }
        }
    }.prettyPrint;

    var arr = try ArrayList(u32).initCapacity(allocator, 8);
    defer arr.deinit();
    var i: u32 = 8;
    while (i < 8 + 8) : (i += 1) {
        arr.appendAssumeCapacity(i);
    }
    var arr_or_maybe = ArrayOrMaybe(u32){ .inl = arr };

    // example of applicative functor
    arr_or_maybe = try array_or_maybe.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 42;
        }
    }.f, arr_or_maybe);
    std.debug.print("arr_or_maybe mapped: ", .{});
    prettyArrayOrMaybe(arr_or_maybe);

    const arr_or_maybe_new = try array_or_maybe.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) * 3.14;
        }
    }.f, arr_or_maybe);
    defer {
        if (arr_or_maybe_new == .inl) {
            arr_or_maybe_new.inl.deinit();
        }
    }
    std.debug.print("arr_or_maybe_new: ", .{});
    prettyArrayOrMaybe(arr_or_maybe_new);

    // example of applicative functor
    const FloatToIntFn = *const fn (f64) u32;
    const fn_array = [_]FloatToIntFn{
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@floor(x));
            }
        }.f,
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@ceil(x * 4.0));
            }
        }.f,
    };

    var arr_fns = try ArrayList(FloatToIntFn).initCapacity(allocator, fn_array.len);
    defer arr_fns.deinit();
    for (fn_array) |f| {
        arr_fns.appendAssumeCapacity(f);
    }
    const or_array_fns = ArrayOrMaybe(FloatToIntFn){ .inl = arr_fns };
    const or_maybe_fns = ArrayOrMaybe(FloatToIntFn){ .inr = fn_array[1] };

    const maybe_array_applied = try array_or_maybe.fapply(or_maybe_fns, arr_or_maybe_new);
    defer {
        if (maybe_array_applied == .inl) {
            maybe_array_applied.inl.deinit();
        }
    }
    std.debug.print("maybe_array_applied: ", .{});
    prettyArrayOrMaybe(maybe_array_applied);

    const array_array_applied = try array_or_maybe.fapply(or_array_fns, arr_or_maybe_new);
    defer {
        if (array_array_applied == .inl) {
            array_array_applied.inl.deinit();
        }
    }
    std.debug.print("array_array_applied: ", .{});
    prettyArrayOrMaybe(array_array_applied);

    const or_maybe_float = ArrayOrMaybe(f64){ .inr = 2.71828 };
    const array_maybe_applied = try array_or_maybe.fapply(or_array_fns, or_maybe_float);
    defer {
        if (array_maybe_applied == .inl) {
            array_maybe_applied.inl.deinit();
        }
    }
    std.debug.print("array_maybe_applied: ", .{});
    prettyArrayOrMaybe(array_maybe_applied);

    const maybe_maybe_applied = try array_or_maybe.fapply(or_maybe_fns, or_maybe_float);
    defer {
        if (maybe_maybe_applied == .inl) {
            maybe_maybe_applied.inl.deinit();
        }
    }
    std.debug.print("maybe_maybe_applied: ", .{});
    prettyArrayOrMaybe(maybe_maybe_applied);
}

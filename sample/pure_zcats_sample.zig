const std = @import("std");
const zcats = @import("zcats");
const pure_zcats = zcats.pure;

const Functor = pure_zcats.Functor;
const Applicative = pure_zcats.Applicative;
const Monad = pure_zcats.Monad;
const NatTrans = pure_zcats.NatTrans;

const ComposeApplicative = pure_zcats.ComposeApplicative;
const ProductFG = pure_zcats.ProductFG;
const ProductApplicative = pure_zcats.ProductApplicative;
const CoproductFG = pure_zcats.CoproductFG;
const CoproductApplicative = pure_zcats.CoproductApplicative;

const Maybe = zcats.Maybe;
const MaybeMonadImpl = pure_zcats.MaybeMonadImpl;
const Array = zcats.Array;
const ArrayMonadImpl = pure_zcats.ArrayMonadImpl;
const MaybeToArrayNatImpl = pure_zcats.MaybeToArrayNatImpl;

pub fn runZCatsSamples() void {
    maybeSample();
    arraySample();
    composeSample();
    productSample();
    coproductSample();
}

fn maybeSample() void {
    const MaybeMonad = Monad(MaybeMonadImpl);

    var maybe_a: ?u32 = 42;
    maybe_a = MaybeMonad.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 10;
        }
    }.f, maybe_a);

    const maybe_b = MaybeMonad.fmap(.NewValMap, struct {
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
    var maybe_applied = MaybeMonad.fapply(f64, u32, maybe_fn, maybe_b);
    std.debug.print("maybe_applied: {any}\n", .{maybe_applied});
    maybe_applied = MaybeMonad.fapply(u32, u32, null, maybe_applied);
    std.debug.print("applied with null function: {any}\n", .{maybe_applied});

    const maybe_binded = MaybeMonad.bind(f64, u32, maybe_b, struct {
        fn f(x: f64) ?u32 {
            return @intFromFloat(@ceil(x * 4.0));
        }
    }.f);
    std.debug.print("maybe_binded: {any}\n", .{maybe_binded});
}

fn arraySample() void {
    const ARRAY_LEN = 4;
    const ArrayF = Array(ARRAY_LEN);
    const ArrayMonad = Monad(ArrayMonadImpl(ARRAY_LEN));

    var arr: ArrayF(u32) = undefined;
    var i: u32 = 0;
    while (i < arr.len) : (i += 1) {
        arr[i] = i;
    }

    // example of functor
    arr = ArrayMonad.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 42;
        }
    }.f, arr);
    std.debug.print("arr inplace mapped: {any}\n", .{arr});

    const arr_f32 = ArrayMonad.fmap(.InplaceMap, struct {
        fn f(a: u32) f32 {
            return @as(f32, @floatFromInt(a)) + 6.18;
        }
    }.f, arr);
    std.debug.print("arr float32 inplace mapped: {any}\n", .{arr_f32});

    arr = ArrayMonad.fmap(.InplaceMap, struct {
        fn f(a: f32) u32 {
            return @as(u32, @intFromFloat(a)) + 58;
        }
    }.f, arr_f32);
    std.debug.print("arr inplace mapped again: {any}\n", .{arr});

    const arr_new = ArrayMonad.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) * 3.14;
        }
    }.f, arr);
    std.debug.print("arr_new: {any}\n", .{arr_new});

    // example of applicative functor
    const FloatToIntFn = *const fn (f64) u32;
    const arr_fns = [_]FloatToIntFn{
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@floor(x));
            }
        }.f,
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@ceil(x + 8.0));
            }
        }.f,
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@ceil(x * 2.0));
            }
        }.f,
        struct {
            fn f(x: f64) u32 {
                return @intFromFloat(@ceil(x * 4.0));
            }
        }.f,
    };

    const arr_applied = ArrayMonad.fapply(f64, u32, arr_fns, arr_new);
    std.debug.print("arr_applied: {any}\n", .{arr_applied});

    const arr_comptime = [_]f64{ 2, 4, 5, 9 };
    const comptime_applied = comptime ArrayMonad.fapply(f64, u32, arr_fns, arr_comptime);
    std.debug.print("comptime_applied: {any}\n", .{comptime_applied});

    // example of monad
    const arr_binded = ArrayMonad.bind(f64, u32, arr_new, struct {
        fn f(a: f64) ArrayF(u32) {
            var arr_b: ArrayF(u32) = undefined;
            var j: usize = 0;
            while (j < arr_b.len) : (j += 1) {
                if ((j & 0x1) == 0) {
                    arr_b[j] = @intFromFloat(@ceil(a * 4.0));
                } else {
                    arr_b[j] = @intFromFloat(@ceil(a * 9.0));
                }
            }
            return arr_b;
        }
    }.f);
    std.debug.print("arr_binded: {any}\n", .{arr_binded});

    const comptime_binded = comptime ArrayMonad.bind(f64, u32, arr_comptime, struct {
        fn f(a: f64) ArrayF(u32) {
            var arr_b: ArrayF(u32) = undefined;
            var j: usize = 0;
            while (j < arr_b.len) : (j += 1) {
                if ((j & 0x1) == 0) {
                    arr_b[j] = @intFromFloat(@ceil(a * 4.0));
                } else {
                    arr_b[j] = @intFromFloat(@ceil(a * 9.0));
                }
            }
            return arr_b;
        }
    }.f);
    std.debug.print("comptime_binded: {any}\n", .{comptime_binded});
}

fn composeSample() void {
    const ARRAY_LEN = 4;
    const ArrayF = Array(ARRAY_LEN);
    const ArrayApplicative = Applicative(ArrayMonadImpl(ARRAY_LEN));
    const MaybeApplicative = Applicative(MaybeMonadImpl);

    const ArrayMaybeApplicative = ComposeApplicative(ArrayApplicative, MaybeApplicative);

    var arr: ArrayF(Maybe(u32)) = undefined;
    var i: u32 = 0;
    while (i < arr.len) : (i += 1) {
        if ((i & 0x1) == 0) {
            arr[i] = i;
        } else {
            arr[i] = null;
        }
    }

    // example of applicative functor
    arr = ArrayMaybeApplicative.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 42;
        }
    }.f, arr);
    std.debug.print("arr mapped: {any}\n", .{arr});

    const arr_new = ArrayMaybeApplicative.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) * 3.14;
        }
    }.f, arr);
    std.debug.print("arr_new: {any}\n", .{arr_new});

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

    var arr_fns: ArrayF(Maybe(FloatToIntFn)) = undefined;
    i = 0;
    for (fn_array) |f| {
        arr_fns[i] = f;
        i += 1;
    }
    while (i < arr_fns.len) : (i += 1) {
        arr_fns[i] = null;
    }

    const arr_applied = ArrayMaybeApplicative.fapply(f64, u32, arr_fns, arr_new);
    std.debug.print("arr_applied: {any}\n", .{arr_applied});

    // pretty print the arr3 with type ArrayF(Maybe(AraayF(A)))
    const prettyPrintArr3 = struct {
        fn prettyPrint(arr3: anytype) void {
            std.debug.print("{{ \n", .{});
            var j: u32 = 0;
            for (arr3) |item| {
                if (item) |o| {
                    std.debug.print(" {{ ", .{});
                    for (o) |a| {
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
    }.prettyPrint;

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
        fns: []IntToIntFn,

        const FnSelf = @This();
        pub fn call(self: *const FnSelf, a: u32) ArrayF(IntToIntFn) {
            _ = a;
            var arr1_fn: ArrayF(IntToIntFn) = undefined;
            var j: usize = 0;
            while (j < arr1_fn.len) : (j += 1) {
                if (j < self.fns.len) {
                    arr1_fn[j] = self.fns[j];
                } else {
                    arr1_fn[j] = self.fns[self.fns.len - 1];
                }
            }
            return arr1_fn;
        }
    }{ .fns = fn_int_array[0..] };
    const arr3_fns = ArrayMaybeApplicative.fmapLam(.NewValMap, intToFns, arr);

    const intToArr = struct {
        fn intToArr(a: u32) ArrayF(u32) {
            var tmp = a;
            var j: u32 = 0;
            var int_arr: ArrayF(u32) = undefined;
            while (j < int_arr.len) : ({
                j += 1;
                tmp += 2;
            }) {
                int_arr[j] = tmp;
            }
            return int_arr;
        }
    }.intToArr;

    const arr3_ints = ArrayMaybeApplicative.fmap(.NewValMap, intToArr, arr_applied);
    // std.debug.print("arr3_ints: {any}\n", .{arr3_ints});

    const ArrayMaybeArrayApplicative = ComposeApplicative(ArrayMaybeApplicative, ArrayApplicative);

    const arr3_appried = ArrayMaybeArrayApplicative.fapply(u32, u32, arr3_fns, arr3_ints);
    std.debug.print("arr3_appried: ", .{});
    prettyPrintArr3(arr3_appried);
}

fn productSample() void {
    const ARRAY_LEN = 4;
    const ArrayF = Array(ARRAY_LEN);
    const ArrayAndMaybe = ProductFG(ArrayF, Maybe);
    const ArrayApplicative = Applicative(ArrayMonadImpl(ARRAY_LEN));
    const MaybeApplicative = Applicative(MaybeMonadImpl);

    const ArrayAndMaybeApplicative = ProductApplicative(ArrayApplicative, MaybeApplicative);

    // pretty print the array maybe tuple with type { ArrayF(A), Maybe(A) }
    const prettyArrayAndMaybe = struct {
        fn prettyPrint(arr_and_maybe: anytype) void {
            std.debug.print("{{ {any}, {any} }}\n", .{ arr_and_maybe[0], arr_and_maybe[1] });
        }
    }.prettyPrint;

    var arr: ArrayF(u32) = undefined;
    var i: u32 = 0;
    while (i < arr.len) : (i += 1) {
        arr[i] = i;
    }
    var arr_and_maybe = ArrayAndMaybe(u32){ arr, 42 };

    // example of applicative functor
    arr_and_maybe = ArrayAndMaybeApplicative.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 42;
        }
    }.f, arr_and_maybe);
    std.debug.print("arr_and_maybe mapped: ", .{});
    prettyArrayAndMaybe(arr_and_maybe);

    const arr_and_maybe_new = ArrayAndMaybeApplicative.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) * 3.14;
        }
    }.f, arr_and_maybe);
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

    var arr_fns: ArrayF(FloatToIntFn) = undefined;
    i = 0;
    while (i < arr_fns.len) : (i += 1) {
        if (i < fn_array.len) {
            arr_fns[i] = fn_array[i];
        } else {
            arr_fns[i] = fn_array[fn_array.len - 1];
        }
    }
    const arr_and_maybe_fns = ArrayAndMaybe(FloatToIntFn){ arr_fns, fn_array[0] };

    const arr_and_maybe_applied = ArrayAndMaybeApplicative.fapply(f64, u32, arr_and_maybe_fns, arr_and_maybe_new);
    std.debug.print("arr_and_maybe_applied: ", .{});
    prettyArrayAndMaybe(arr_and_maybe_applied);
}

fn coproductSample() void {
    const ARRAY_LEN = 4;
    const ArrayF = Array(ARRAY_LEN);
    const ArrayOrMaybe = CoproductFG(ArrayF, Maybe);
    const ArrayApplicative = Applicative(ArrayMonadImpl(ARRAY_LEN));
    const MaybeApplicative = Applicative(MaybeMonadImpl);
    const NatMaybeToArray = NatTrans(MaybeToArrayNatImpl(ARRAY_LEN));

    const ArrayOrMaybeApplicative = CoproductApplicative(ArrayApplicative, MaybeApplicative, NatMaybeToArray);

    // pretty print the arr_or_maybe with type Coproduct(ArrayF, Maybe)
    const prettyArrayOrMaybe = struct {
        fn prettyPrint(arr_or_maybe: anytype) void {
            if (arr_or_maybe == .inl) {
                std.debug.print("{{ inl: {any} }}\n", .{arr_or_maybe.inl});
            } else {
                std.debug.print("{{ inr: {any} }}\n", .{arr_or_maybe.inr});
            }
        }
    }.prettyPrint;

    var arr: ArrayF(u32) = undefined;
    var i: u32 = 0;
    while (i < arr.len) : (i += 1) {
        arr[i] = i;
    }
    var arr_or_maybe = ArrayOrMaybe(u32){ .inl = arr };

    // example of applicative functor
    arr_or_maybe = ArrayOrMaybeApplicative.fmap(.InplaceMap, struct {
        fn f(a: u32) u32 {
            return a + 42;
        }
    }.f, arr_or_maybe);
    std.debug.print("arr_or_maybe mapped: ", .{});
    prettyArrayOrMaybe(arr_or_maybe);

    const arr_or_maybe_new = ArrayOrMaybeApplicative.fmap(.NewValMap, struct {
        fn f(a: u32) f64 {
            return @as(f64, @floatFromInt(a)) * 3.14;
        }
    }.f, arr_or_maybe);
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

    var arr_fns: ArrayF(FloatToIntFn) = undefined;
    i = 0;
    while (i < arr_fns.len) : (i += 1) {
        if (i < fn_array.len) {
            arr_fns[i] = fn_array[i];
        } else {
            arr_fns[i] = fn_array[fn_array.len - 1];
        }
    }
    const or_array_fns = ArrayOrMaybe(FloatToIntFn){ .inl = arr_fns };
    const or_maybe_fns = ArrayOrMaybe(FloatToIntFn){ .inr = fn_array[1] };

    const maybe_array_applied = ArrayOrMaybeApplicative.fapply(f64, u32, or_maybe_fns, arr_or_maybe_new);
    std.debug.print("maybe_array_applied: ", .{});
    prettyArrayOrMaybe(maybe_array_applied);

    const array_array_applied = ArrayOrMaybeApplicative.fapply(f64, u32, or_array_fns, arr_or_maybe_new);
    std.debug.print("array_array_applied: ", .{});
    prettyArrayOrMaybe(array_array_applied);

    const or_maybe_float = ArrayOrMaybe(f64){ .inr = 2.71828 };
    const array_maybe_applied = ArrayOrMaybeApplicative.fapply(f64, u32, or_array_fns, or_maybe_float);
    std.debug.print("array_maybe_applied: ", .{});
    prettyArrayOrMaybe(array_maybe_applied);

    const maybe_maybe_applied = ArrayOrMaybeApplicative.fapply(f64, u32, or_maybe_fns, or_maybe_float);
    std.debug.print("maybe_maybe_applied: ", .{});
    prettyArrayOrMaybe(maybe_maybe_applied);
}

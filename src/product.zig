const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const maybe = @import("maybe.zig");
const listm = @import("array_list_monad.zig");
const testu = @import("test_utils.zig");

const testing = std.testing;
const assert = std.debug.assert;
const TCtor = base.TCtor;
var maybe_error = maybe.maybe_error;

const MapFnKind = base.MapFnKind;

const Functor = functor.Functor;
const FunctorFromImpl = functor.FunctorFromImpl;
const FunctorFxTypes = functor.FunctorFxTypes;
const Applicative = applicative.Applicative;
const ApplicativeFromImpl = applicative.ApplicativeFromImpl;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;

/// Get a Product Type constructor from two Type constructor, the parameter
/// F and G are one parameter Type consturctor.
pub fn ProductFG(comptime F: TCtor, comptime G: TCtor) TCtor {
    return struct {
        fn Producted(comptime A: type) type {
            return struct { F(A), G(A) };
        }
    }.Producted;
}

/// Get tuple of left and right type of product
pub fn getProductTypeTuple(comptime P: type) struct { type, type } {
    const info = @typeInfo(P);
    comptime assert(info == .Struct and info.Struct.is_tuple == true);
    comptime assert(info.Struct.fields.len == 2);

    const l_type = info.Struct.fields[0].type;
    const r_type = info.Struct.fields[1].type;
    return .{ l_type, r_type };
}

pub fn ProductFunctorImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        instanceF: ImplF,
        instanceG: ImplG,

        const Self = @This();
        const FunctorF = FunctorFromImpl(ImplF);
        const FunctorG = FunctorFromImpl(ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = ProductFG(ImplF.F, ImplG.F);

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
        /// ImplG.
        pub fn BaseType(comptime FGA: type) type {
            const l_type, const r_type = getProductTypeTuple(FGA);
            comptime assert(ImplF.BaseType(l_type) == ImplG.BaseType(r_type));
            return ImplF.BaseType(l_type);
        }

        /// Error set of ProductFunctorImpl, it is a merge set of error sets in
        /// ImplF and ImplG
        pub const Error: ?type = maybe_error.mappend(ImplF.Error, ImplG.Error);

        const FxTypes = FunctorFxTypes(F, Error);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        pub fn deinitFa(
            fga: anytype, // (F(A), G(A))
            comptime free_fn: *const fn (BaseType(@TypeOf(fga))) void,
        ) void {
            ImplF.deinitFa(fga[0], free_fn);
            ImplG.deinitFa(fga[1], free_fn);
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            const fgb_0 = if (ImplF.Error == null)
                self.instanceF.fmap(K, map_fn, fga[0])
            else
                try self.instanceF.fmap(K, map_fn, fga[0]);

            const fgb_1 = if (ImplG.Error == null)
                self.instanceG.fmap(K, map_fn, fga[1])
            else
                try self.instanceG.fmap(K, map_fn, fga[1]);

            return .{ fgb_0, fgb_1 };
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            const fgb_0 = if (ImplF.Error == null)
                self.instanceF.fmapLam(K, map_lam, fga[0])
            else
                try self.instanceF.fmapLam(K, map_lam, fga[0]);

            const fgb_1 = if (ImplG.Error == null)
                self.instanceG.fmapLam(K, map_lam, fga[1])
            else
                try self.instanceG.fmapLam(K, map_lam, fga[1]);

            return .{ fgb_0, fgb_1 };
        }
    };
}

pub fn ProductApplicativeImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        functor_sup: SupImpl,

        const Self = @This();
        pub const SupImpl = ProductFunctorImpl(ImplF, ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = SupImpl.F;

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
        /// ImplG.
        pub const BaseType = SupImpl.BaseType;

        /// Error set of ProductApplicativeImpl, it is a merge set of error sets in
        /// ImplF and ImplG
        pub const Error: ?type = SupImpl.Error;

        pub const FaType = SupImpl.FaType;
        pub const FbType = SupImpl.FbType;
        pub const FaLamType = SupImpl.FaLamType;
        pub const FbLamType = SupImpl.FbLamType;

        const AFxTypes = ApplicativeFxTypes(F, Error);
        pub const APaType = AFxTypes.APaType;
        pub const AFbType = AFxTypes.AFbType;

        pub fn deinitFa(
            fga: anytype, // (F(A), G(A))
            comptime free_fn: *const fn (BaseType(@TypeOf(fga))) void,
        ) void {
            SupImpl.deinitFa(fga, free_fn);
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return self.functor_sup.fmap(K, map_fn, fga);
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return self.functor_sup.fmapLam(K, map_lam, fga);
        }

        pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
            const pure_0 = if (ImplF.Error == null)
                self.functor_sup.instanceF.pure(a)
            else
                try self.functor_sup.instanceF.pure(a);

            const pure_1 = if (ImplG.Error == null)
                self.functor_sup.instanceG.pure(a)
            else
                try self.functor_sup.instanceG.pure(a);

            return .{ pure_0, pure_1 };
        }

        pub fn fapply(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: F(*const fn (A) B),
            fga: F(A),
        ) AFbType(B) {
            const fgb_0 = if (ImplF.Error == null)
                self.functor_sup.instanceF.fapply(A, B, fgf[0], fga[0])
            else
                try self.functor_sup.instanceF.fapply(A, B, fgf[0], fga[0]);

            const fgb_1 = if (ImplG.Error == null)
                self.functor_sup.instanceG.fapply(A, B, fgf[1], fga[1])
            else
                try self.functor_sup.instanceG.fapply(A, B, fgf[1], fga[1]);

            return .{ fgb_0, fgb_1 };
        }

        pub fn fapplyLam(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) AFbType(B) {
            const fgb_0 = if (ImplF.Error == null)
                self.functor_sup.instanceF.fapplyLam(A, B, fgf[0], fga[0])
            else
                try self.functor_sup.instanceF.fapplyLam(A, B, fgf[0], fga[0]);

            const fgb_1 = if (ImplG.Error == null)
                self.functor_sup.instanceG.fapplyLam(A, B, fgf[1], fga[1])
            else
                try self.functor_sup.instanceG.fapplyLam(A, B, fgf[1], fga[1]);

            return .{ fgb_0, fgb_1 };
        }
    };
}

/// Get a Product Functor from two Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn ProductFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const FGImpl = ProductFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return FunctorFromImpl(FGImpl);
}

/// Get a Product Applicative from two Applicative, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn ProductApplicative(comptime ApplicativeF: type, comptime ApplicativeG: type) type {
    const FGImpl = ProductApplicativeImpl(ApplicativeF.InstanceImpl, ApplicativeG.InstanceImpl);
    return ApplicativeFromImpl(FGImpl);
}

// These functions are defined for unit test
const add4 = testu.add4;
const add10 = testu.add10;
const mul2 = testu.mul2;
const mul3 = testu.mul3;
const add_pi_f64 = testu.add_pi_f64;
const add_e_f64 = testu.add_e_f64;

const monad = @import("monad.zig");
const ArrayListMonadImpl = listm.ArrayListMonadImpl;
const MaybeMonadImpl = maybe.MaybeMonadImpl;

const Maybe = base.Maybe;
const ArrayList = std.ArrayList;

test "Compose Functor fmap" {
    // test (ArrayList, Maybe) product functor
    const allocator = testing.allocator;
    const ArrayAndMaybe = ProductFG(ArrayList, Maybe);
    const ArrayListFunctor = Functor(ArrayList);
    const MaybeFunctor = Functor(Maybe);
    const ArrayListAndMaybeFunctor = ProductFunctor(ArrayListFunctor, MaybeFunctor);

    var array_and_maybe = ArrayListAndMaybeFunctor.InstanceImpl{
        .instanceF = .{ .allocator = allocator },
        .instanceG = .{},
    };

    var array_a = ArrayList(u32).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]u32{ 1, 2, 3, 4 });

    var arr_maybe_a = ArrayAndMaybe(u32){ array_a, 42 };
    arr_maybe_a = try array_and_maybe.fmap(.InplaceMap, add10, arr_maybe_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 11, 12, 13, 14 }, arr_maybe_a[0].items);
    try testing.expectEqual(52, arr_maybe_a[1]);

    arr_maybe_a[1] = null; // (array_a, null)
    arr_maybe_a = try array_and_maybe.fmap(.InplaceMap, mul3, arr_maybe_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 33, 36, 39, 42 }, arr_maybe_a[0].items);
    try testing.expectEqual(null, arr_maybe_a[1]);

    var arr_maybe_b = try array_and_maybe.fmap(.NewValMap, add4, arr_maybe_a);
    defer arr_maybe_b[0].deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 37, 40, 43, 46 }, arr_maybe_b[0].items);
    try testing.expectEqual(null, arr_maybe_b[1]);

    arr_maybe_b[1] = 18; // (array_a, 18)
    const arr_maybe_c = try array_and_maybe.fmap(.NewValMap, mul2, arr_maybe_b);
    defer arr_maybe_c[0].deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 74, 80, 86, 92 }, arr_maybe_c[0].items);
    try testing.expectEqual(36, arr_maybe_c[1]);
}

test "Compose Applicative pure and fapply" {
    // const IntToIntFn = *const fn (u32) u32;
    const IntToFloatFn = *const fn (u32) f64;

    // test (ArrayList, Maybe) product applicative
    const allocator = testing.allocator;
    const ArrayAndMaybe = ProductFG(ArrayList, Maybe);
    const ArrayListApplicative = Applicative(ArrayList);
    const MaybeApplicative = Applicative(Maybe);
    const ArrayListAndMaybeApplicative = ProductApplicative(ArrayListApplicative, MaybeApplicative);

    var array_and_maybe = ArrayListAndMaybeApplicative.InstanceImpl{ .functor_sup = .{
        .instanceF = .{ .allocator = allocator },
        .instanceG = .{},
    } };

    const arr_maybe_pured = try array_and_maybe.pure(@as(f32, 3.14));
    defer arr_maybe_pured[0].deinit();
    try testing.expectEqualSlices(f32, &[_]f32{3.14}, arr_maybe_pured[0].items);
    try testing.expectEqual(3.14, arr_maybe_pured[1]);

    var array_a = ArrayList(u32).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]u32{ 1, 2, 3, 4 });
    var arr_maybe_a = ArrayAndMaybe(u32){ array_a, 42 };

    var array_fns = ArrayList(IntToFloatFn).init(allocator);
    defer array_fns.deinit();
    try array_fns.appendSlice(&[_]IntToFloatFn{ add_pi_f64, add_e_f64 });
    var arr_maybe_fns = ArrayAndMaybe(IntToFloatFn){ array_fns, add_pi_f64 };

    const arr_maybe_b = try array_and_maybe.fapply(u32, f64, arr_maybe_fns, arr_maybe_a);
    defer arr_maybe_b[0].deinit();
    for (&[_]f64{
        // 0..3
        4.14,    5.14,    6.14,    7.14,
        // 4..7
        3.71828, 4.71828, 5.71828, 6.71828,
    }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, arr_maybe_b[0].items[i], std.math.floatEps(f64));
    }
    try testing.expectEqual(45.14, arr_maybe_b[1]);

    arr_maybe_a[1] = null; // (array_a, null)
    const arr_maybe_c = try array_and_maybe.fapply(u32, f64, arr_maybe_fns, arr_maybe_a);
    defer arr_maybe_c[0].deinit();
    for (&[_]f64{
        // 0..3
        4.14,    5.14,    6.14,    7.14,
        // 4..7
        3.71828, 4.71828, 5.71828, 6.71828,
    }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, arr_maybe_c[0].items[i], std.math.floatEps(f64));
    }
    try testing.expectEqual(null, arr_maybe_c[1]);

    arr_maybe_a[1] = 23; // (array_a, 23)
    arr_maybe_fns[1] = null; // (array_fns, null)
    const arr_maybe_d = try array_and_maybe.fapply(u32, f64, arr_maybe_fns, arr_maybe_a);
    defer arr_maybe_d[0].deinit();
    for (&[_]f64{
        // 0..3
        4.14,    5.14,    6.14,    7.14,
        // 4..7
        3.71828, 4.71828, 5.71828, 6.71828,
    }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, arr_maybe_d[0].items[i], std.math.floatEps(f64));
    }
    try testing.expectEqual(null, arr_maybe_d[1]);
}

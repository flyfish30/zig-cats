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

/// Get a Coproduct Type constructor from two Type constructor, the parameter
/// F and G are one parameter Type consturctor.
pub fn CoproductFG(comptime F: TCtor, comptime G: TCtor) TCtor {
    return struct {
        fn Coproducted(comptime A: type) type {
            return union(enum) {
                inl: F(A),
                inr: G(A),
            };
        }
    }.Coproducted;
}

/// Get tuple of left and right type of coproduct
pub fn getCoproductTypeTuple(comptime U: type) struct { type, type } {
    const info = @typeInfo(U);
    comptime assert(info == .@"union");
    comptime assert(info.@"union".fields.len == 2);

    const l_type = info.@"union".fields[0].type;
    const r_type = info.@"union".fields[1].type;
    return .{ l_type, r_type };
}

pub fn CoproductFunctorImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        instanceF: ImplF,
        instanceG: ImplG,

        const Self = @This();
        const FunctorF = FunctorFromImpl(ImplF);
        const FunctorG = FunctorFromImpl(ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = CoproductFG(ImplF.F, ImplG.F);

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
        /// ImplG.
        pub fn BaseType(comptime FGA: type) type {
            const l_type, const r_type = getCoproductTypeTuple(FGA);
            comptime assert(ImplF.BaseType(l_type) == ImplG.BaseType(r_type));
            return ImplF.BaseType(l_type);
        }

        /// Error set of CoproductFunctorImpl, it is a merge set of error sets in
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
            self: *const Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return switch (fga) {
                .inl => |fa| if (ImplF.Error == null)
                    .{ .inl = self.instanceF.fmap(K, map_fn, fa) }
                else
                    .{ .inl = try self.instanceF.fmap(K, map_fn, fa) },
                .inr => |ga| if (ImplG.Error == null)
                    .{ .inr = self.instanceG.fmap(K, map_fn, ga) }
                else
                    .{ .inr = try self.instanceG.fmap(K, map_fn, ga) },
            };
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return switch (fga) {
                .inl => |fa| if (ImplF.Error == null)
                    .{ .inl = self.instanceF.fmapLam(K, map_lam, fa) }
                else
                    .{ .inl = try self.instanceF.fmapLam(K, map_lam, fa) },
                .inr => |ga| if (ImplG.Error == null)
                    .{ .inr = self.instanceG.fmapLam(K, map_lam, ga) }
                else
                    .{ .inr = try self.instanceG.fmapLam(K, map_lam, ga) },
            };
        }
    };
}

pub fn CoproductApplicativeImpl(
    comptime ImplF: type,
    comptime ImplG: type,
    comptime ImplNat: type,
) type {
    return struct {
        functor_sup: SupImpl,
        /// The ImplNat type must is void for instance of Coproduct Functor
        natural_gf: ImplNat,

        const Self = @This();
        pub const SupImpl = CoproductFunctorImpl(ImplF, ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = SupImpl.F;

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
        /// ImplG.
        pub const BaseType = SupImpl.BaseType;

        /// Error set of CoproductApplicativeImpl, it is a merge set of error sets in
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
            self: *const Self,
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

        pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
            return if (ImplG.Error == null)
                .{ .inr = self.functor_sup.instanceG.pure(a) }
            else
                .{ .inr = try self.functor_sup.instanceG.pure(a) };
        }

        pub fn fapply(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: F(*const fn (A) B),
            fga: F(A),
        ) AFbType(B) {
            const FnType = BaseType(@TypeOf(fgf));
            return switch (fgf) {
                .inl => |ff| switch (fga) {
                    .inl => |fa| if (ImplF.Error == null)
                        .{ .inl = self.functor_sup.instanceF.fapply(A, B, ff, fa) }
                    else
                        .{ .inl = try self.functor_sup.instanceF.fapply(A, B, ff, fa) },
                    .inr => |ga| {
                        // fa is ArrayList(A), so we should be free it.
                        const fa = if (ImplNat.Error == null)
                            self.natural_gf.trans(A, ga)
                        else
                            try self.natural_gf.trans(A, ga);
                        defer base.deinitOrUnref(fa);
                        return if (ImplF.Error == null)
                            .{ .inl = self.functor_sup.instanceF.fapply(A, B, ff, fa) }
                        else
                            .{ .inl = try self.functor_sup.instanceF.fapply(A, B, ff, fa) };
                    },
                },
                .inr => |gf| switch (fga) {
                    .inl => |fa| {
                        // ff is ArrayList(FnType), so we should be free it.
                        const ff = if (ImplNat.Error == null)
                            self.natural_gf.trans(FnType, gf)
                        else
                            try self.natural_gf.trans(FnType, gf);
                        defer base.deinitOrUnref(ff);
                        return if (ImplF.Error == null)
                            .{ .inl = self.functor_sup.instanceF.fapply(A, B, ff, fa) }
                        else
                            .{ .inl = try self.functor_sup.instanceF.fapply(A, B, ff, fa) };
                    },
                    .inr => |ga| if (ImplG.Error == null)
                        .{ .inr = self.functor_sup.instanceG.fapply(A, B, gf, ga) }
                    else
                        .{ .inr = try self.functor_sup.instanceG.fapply(A, B, gf, ga) },
                },
            };
        }

        pub fn fapplyLam(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) AFbType(B) {
            const LamType = BaseType(@TypeOf(fgf));
            return switch (fgf) {
                .inl => |ff| switch (fga) {
                    .inl => |fa| if (ImplF.Error == null)
                        .{ .inl = self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) }
                    else
                        .{ .inl = try self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) },
                    .inr => |ga| {
                        // fa is ArrayList(A), so we should be free it.
                        const fa = if (ImplNat.Error == null)
                            self.natural_gf.trans(A, ga)
                        else
                            try self.natural_gf.trans(A, ga);
                        defer fa.deinit();
                        return if (ImplF.Error == null)
                            .{ .inl = self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) }
                        else
                            .{ .inl = try self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) };
                    },
                },
                .inr => |gf| switch (fga) {
                    .inl => |fa| {
                        // ff is ArrayList(FnType), so we should be free it.
                        const ff = if (ImplNat.Error == null)
                            self.natural_gf.trans(LamType, gf)
                        else
                            try self.natural_gf.trans(LamType, gf);
                        defer ff.deinit();
                        return if (ImplF.Error == null)
                            .{ .inl = self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) }
                        else
                            .{ .inl = try self.functor_sup.instanceF.fapplyLam(A, B, ff, fa) };
                    },
                    .inr => |ga| if (ImplG.Error == null)
                        .{ .inr = self.functor_sup.instanceG.fapplyLam(A, B, gf, ga) }
                    else
                        .{ .inr = try self.functor_sup.instanceG.fapplyLam(A, B, gf, ga) },
                },
            };
        }
    };
}

/// Get a Coproduct Functor from two Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn CoproductFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const FGImpl = CoproductFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return FunctorFromImpl(FGImpl);
}

/// Get a Coproduct Applicative from two Applicative, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn CoproductApplicative(
    comptime ApplicativeF: type,
    comptime ApplicativeG: type,
    comptime NaturalGF: type,
) type {
    const FGImpl = CoproductApplicativeImpl(
        ApplicativeF.InstanceImpl,
        ApplicativeG.InstanceImpl,
        NaturalGF.InstanceImpl,
    );
    return ApplicativeFromImpl(FGImpl);
}

// These functions are defined for unit test
const add4 = testu.add4;
const add10 = testu.add10;
const mul2 = testu.mul2;
const mul3 = testu.mul3;
const add_pi_f64 = testu.add_pi_f64;
const mul_pi_f64 = testu.mul_pi_f64;
const add_e_f64 = testu.add_e_f64;

const monad = @import("monad.zig");
const NatTrans = functor.NatTrans;
const MaybeToArrayListNatImpl = functor.MaybeToArrayListNatImpl;
const ArrayListMonadImpl = listm.ArrayListMonadImpl;
const MaybeMonadImpl = maybe.MaybeMonadImpl;

const Maybe = base.Maybe;
const ArrayList = std.ArrayList;

test "Compose Functor fmap" {
    // test (ArrayList, Maybe) product functor
    const allocator = testing.allocator;
    const ArrayOrMaybe = CoproductFG(ArrayList, Maybe);
    const ArrayListFunctor = Functor(ArrayList);
    const MaybeFunctor = Functor(Maybe);
    const ArrayListOrMaybeFunctor = CoproductFunctor(ArrayListFunctor, MaybeFunctor);

    const array_or_maybe = ArrayListOrMaybeFunctor.InstanceImpl{
        .instanceF = .{ .allocator = allocator },
        .instanceG = .{},
    };

    var array_a = ArrayList(u32).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]u32{ 1, 2, 3, 4 });

    var or_array_a = ArrayOrMaybe(u32){ .inl = array_a };
    or_array_a = try array_or_maybe.fmap(.InplaceMap, add10, or_array_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 11, 12, 13, 14 }, or_array_a.inl.items);

    var or_maybe_a = ArrayOrMaybe(u32){ .inr = 42 };
    or_maybe_a = try array_or_maybe.fmap(.InplaceMap, mul3, or_maybe_a);
    try testing.expectEqual(126, or_maybe_a.inr);

    var or_maybe_b = ArrayOrMaybe(u32){ .inr = null };
    or_maybe_b = try array_or_maybe.fmap(.InplaceMap, mul3, or_maybe_b);
    try testing.expectEqual(null, or_maybe_b.inr);

    const or_array_b = try array_or_maybe.fmap(.NewValMap, add4, or_array_a);
    defer or_array_b.inl.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 15, 16, 17, 18 }, or_array_b.inl.items);

    const or_maybe_c = try array_or_maybe.fmap(.NewValMap, mul2, or_maybe_a);
    try testing.expectEqual(252, or_maybe_c.inr);

    const or_maybe_d = try array_or_maybe.fmap(.NewValMap, mul2, or_maybe_b);
    try testing.expectEqual(null, or_maybe_d.inr);
}

test "Compose Applicative pure and fapply" {
    // const IntToIntFn = *const fn (u32) u32;
    const IntToFloatFn = *const fn (u32) f64;

    // test (ArrayList, Maybe) product applicative
    const allocator = testing.allocator;
    const ArrayOrMaybe = CoproductFG(ArrayList, Maybe);
    const ArrayListApplicative = Applicative(ArrayList);
    const MaybeApplicative = Applicative(Maybe);
    const NatMaybeToArray = NatTrans(MaybeToArrayListNatImpl);
    const ArrayListOrMaybeApplicative = CoproductApplicative(
        ArrayListApplicative,
        MaybeApplicative,
        NatMaybeToArray,
    );

    const array_or_maybe = ArrayListOrMaybeApplicative.InstanceImpl{
        .functor_sup = .{
            // ArrayList Applicative instance
            .instanceF = .{ .allocator = allocator },
            // Maybe Applicative instance
            .instanceG = .{},
        },
        // NatMaybeToArray Applicative instance
        .natural_gf = .{ .instanceArray = .{ .allocator = allocator } },
    };

    const arr_maybe_pured = try array_or_maybe.pure(@as(f32, 3.14));
    try testing.expectEqual(3.14, arr_maybe_pured.inr);

    var array_a = ArrayList(u32).init(allocator);
    defer array_a.deinit();
    try array_a.appendSlice(&[_]u32{ 1, 2, 3, 4 });
    const or_array_a = ArrayOrMaybe(u32){ .inl = array_a };
    const or_maybe_a = ArrayOrMaybe(u32){ .inr = 7 };

    var array_fns = ArrayList(IntToFloatFn).init(allocator);
    defer array_fns.deinit();
    try array_fns.appendSlice(&[_]IntToFloatFn{ add_pi_f64, add_e_f64 });
    const or_array_fns = ArrayOrMaybe(IntToFloatFn){ .inl = array_fns };
    const or_maybe_fns = ArrayOrMaybe(IntToFloatFn){ .inr = mul_pi_f64 };

    const array_array_a = try array_or_maybe.fapply(u32, f64, or_array_fns, or_array_a);
    defer array_array_a.inl.deinit();
    for (&[_]f64{
        // 0..3
        4.14,    5.14,    6.14,    7.14,
        // 4..7
        3.71828, 4.71828, 5.71828, 6.71828,
    }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_array_a.inl.items[i], std.math.floatEps(f64));
    }

    const maybe_array_a = try array_or_maybe.fapply(u32, f64, or_maybe_fns, or_array_a);
    defer maybe_array_a.inl.deinit();
    for (&[_]f64{ 3.14, 6.28, 9.42, 12.56 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, maybe_array_a.inl.items[i], std.math.floatEps(f64));
    }

    const array_maybe_a = try array_or_maybe.fapply(u32, f64, or_array_fns, or_maybe_a);
    defer array_maybe_a.inl.deinit();
    for (&[_]f64{ 10.14, 9.71828 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_maybe_a.inl.items[i], std.math.floatEps(f64));
    }

    const maybe_maybe_a = try array_or_maybe.fapply(u32, f64, or_maybe_fns, or_maybe_a);
    try testing.expectEqual(21.98, maybe_maybe_a.inr);
}

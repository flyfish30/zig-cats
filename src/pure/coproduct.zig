const std = @import("std");
const base = @import("../base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");

const testing = std.testing;
const assert = std.debug.assert;
const TCtor = base.TCtor;

const MapFnKind = base.MapFnKind;

const Functor = functor.Functor;
const FunctorFxTypes = functor.FunctorFxTypes;
const Applicative = applicative.Applicative;

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
    comptime assert(info == .Union);
    comptime assert(info.Union.fields.len == 2);

    const l_type = info.Union.fields[0].type;
    const r_type = info.Union.fields[1].type;
    return .{ l_type, r_type };
}

pub fn CoproductFunctorImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
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

        pub const FxTypes = FunctorFxTypes(F);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        pub fn deinitFa(
            fga: anytype, // (F(A), G(A))
            comptime free_fn: fn (BaseType(@TypeOf(fga))) void,
        ) void {
            ImplF.deinitFa(fga[0], free_fn);
            ImplG.deinitFa(fga[1], free_fn);
        }

        pub fn fmap(
            comptime K: MapFnKind,
            map_fn: anytype,
            fga: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            return switch (fga) {
                .inl => |fa| .{ .inl = ImplF.fmap(K, map_fn, fa) },
                .inr => |ga| .{ .inr = ImplG.fmap(K, map_fn, ga) },
            };
        }

        pub fn fmapLam(
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return switch (fga) {
                .inl => |fa| .{ .inl = ImplF.fmapLam(K, map_lam, fa) },
                .inr => |ga| .{ .inr = ImplG.fmapLam(K, map_lam, ga) },
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
        pub const SupImpl = CoproductFunctorImpl(ImplF, ImplG);

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = SupImpl.F;

        /// Get base type of F(A), it is must just is A.
        /// In this instance, type F(A) is product (F(A), G(A)) by ImplF and
        /// ImplG.
        pub const BaseType = SupImpl.BaseType;

        pub const FaType = SupImpl.FaType;
        pub const FbType = SupImpl.FbType;
        pub const FaLamType = SupImpl.FaLamType;
        pub const FbLamType = SupImpl.FbLamType;

        pub const deinitFa = SupImpl.deinitFa;
        pub const fmap = SupImpl.fmap;
        pub const fmapLam = SupImpl.fmapLam;

        pub fn pure(a: anytype) F(@TypeOf(a)) {
            return .{ .inr = ImplG.pure(a) };
        }

        pub fn fapply(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: F(*const fn (A) B),
            fga: F(A),
        ) F(B) {
            const FnType = BaseType(@TypeOf(fgf));
            return switch (fgf) {
                .inl => |ff| switch (fga) {
                    .inl => |fa| .{ .inl = ImplF.fapply(A, B, ff, fa) },
                    .inr => |ga| {
                        const fa = ImplNat.trans(A, ga);
                        return .{ .inl = ImplF.fapply(A, B, ff, fa) };
                    },
                },
                .inr => |gf| switch (fga) {
                    .inl => |fa| {
                        const ff = ImplNat.trans(FnType, gf);
                        return .{ .inl = ImplF.fapply(A, B, ff, fa) };
                    },
                    .inr => |ga| .{ .inr = ImplG.fapply(A, B, gf, ga) },
                },
            };
        }

        pub fn fapplyLam(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) F(B) {
            const LamType = BaseType(@TypeOf(fgf));
            return switch (fgf) {
                .inl => |ff| switch (fga) {
                    .inl => |fa| .{ .inl = ImplF.fapplyLam(A, B, ff, fa) },
                    .inr => |ga| {
                        const fa = ImplNat.trans(A, ga);
                        return .{ .inl = ImplF.fapplyLam(A, B, ff, fa) };
                    },
                },
                .inr => |gf| switch (fga) {
                    .inl => |fa| {
                        const ff = ImplNat.trans(LamType, gf);
                        return .{ .inl = ImplF.fapplyLam(A, B, ff, fa) };
                    },
                    .inr => |ga| .{ .inr = ImplG.fapplyLam(A, B, gf, ga) },
                },
            };
        }
    };
}

/// Get a Coproduct Functor from two Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn CoproductFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const ImplFG = CoproductFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return Functor(ImplFG);
}

/// Get a Coproduct Applicative from two Applicative, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn CoproductApplicative(
    comptime ApplicativeF: type,
    comptime ApplicativeG: type,
    comptime NaturalGF: type,
) type {
    const ImplFG = CoproductApplicativeImpl(
        ApplicativeF.InstanceImpl,
        ApplicativeG.InstanceImpl,
        NaturalGF.InstanceImpl,
    );
    return Applicative(ImplFG);
}

// These functions are defined for unit test
const add4 = struct {
    fn f(a: u32) u32 {
        return a + 4;
    }
}.f;

const add10 = struct {
    fn f(a: u32) u32 {
        return a + 10;
    }
}.f;

const mul2 = struct {
    fn f(a: u32) u32 {
        return a * 2;
    }
}.f;

const mul3 = struct {
    fn f(a: u32) u32 {
        return a * 3;
    }
}.f;

const add_pi_f32 = struct {
    fn f(a: u32) f32 {
        return @as(f32, @floatFromInt(a)) + 3.14;
    }
}.f;

const add_pi_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) + 3.14;
    }
}.f;

const mul_pi_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) * 3.14;
    }
}.f;

const add_e_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) + 2.71828;
    }
}.f;

const mul_e_f64 = struct {
    fn f(a: u32) f64 {
        return @as(f64, @floatFromInt(a)) * 2.71828;
    }
}.f;

const monad = @import("monad.zig");
const NatTrans = functor.NatTrans;
const MaybeToArrayNatImpl = functor.MaybeToArrayNatImpl;
const ArrayMonadImpl = monad.ArrayMonadImpl;
const MaybeMonadImpl = monad.MaybeMonadImpl;

const Maybe = base.Maybe;
const Array = base.Array;
const ARRAY_LEN = 4;
const ArrayF = Array(ARRAY_LEN);

test "Compose Functor fmap" {
    // test (ArrayF, Maybe) product functor
    const ArrayOrMaybe = CoproductFG(ArrayF, Maybe);
    const ArrayFunctor = Functor(ArrayMonadImpl(ARRAY_LEN));
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const ArrayOrMaybeFunctor = CoproductFunctor(ArrayFunctor, MaybeFunctor);

    const array_a = ArrayF(u32){ 1, 2, 3, 4 };

    var or_array_a = ArrayOrMaybe(u32){ .inl = array_a };
    or_array_a = ArrayOrMaybeFunctor.fmap(.InplaceMap, add10, or_array_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 11, 12, 13, 14 }, &or_array_a.inl);

    var or_maybe_a = ArrayOrMaybe(u32){ .inr = 42 };
    or_maybe_a = ArrayOrMaybeFunctor.fmap(.InplaceMap, mul3, or_maybe_a);
    try testing.expectEqual(126, or_maybe_a.inr);

    var or_maybe_b = ArrayOrMaybe(u32){ .inr = null };
    or_maybe_b = ArrayOrMaybeFunctor.fmap(.InplaceMap, mul3, or_maybe_b);
    try testing.expectEqual(null, or_maybe_b.inr);

    const or_array_b = ArrayOrMaybeFunctor.fmap(.NewValMap, add4, or_array_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 15, 16, 17, 18 }, &or_array_b.inl);

    const or_maybe_c = ArrayOrMaybeFunctor.fmap(.NewValMap, mul2, or_maybe_a);
    try testing.expectEqual(252, or_maybe_c.inr);

    const or_maybe_d = ArrayOrMaybeFunctor.fmap(.NewValMap, mul2, or_maybe_b);
    try testing.expectEqual(null, or_maybe_d.inr);
}

test "Compose Applicative pure and fapply" {
    // const IntToIntFn = *const fn (u32) u32;
    const IntToFloatFn = *const fn (u32) f64;

    // test (ArrayF, Maybe) product applicative
    const ArrayOrMaybe = CoproductFG(ArrayF, Maybe);
    const ArrayApplicative = Applicative(ArrayMonadImpl(ARRAY_LEN));
    const MaybeApplicative = Applicative(MaybeMonadImpl);
    const NatMaybeToArray = NatTrans(MaybeToArrayNatImpl(ARRAY_LEN));
    const ArrayOrMaybeApplicative = CoproductApplicative(
        ArrayApplicative,
        MaybeApplicative,
        NatMaybeToArray,
    );

    const arr_maybe_pured = ArrayOrMaybeApplicative.pure(@as(f32, 3.14));
    try testing.expectEqual(3.14, arr_maybe_pured.inr);

    const array_a = ArrayF(u32){ 1, 2, 3, 4 };
    const or_array_a = ArrayOrMaybe(u32){ .inl = array_a };
    const or_maybe_a = ArrayOrMaybe(u32){ .inr = 7 };

    const array_fns = ArrayF(IntToFloatFn){ add_pi_f64, mul_pi_f64, add_e_f64, mul_e_f64 };
    const or_array_fns = ArrayOrMaybe(IntToFloatFn){ .inl = array_fns };
    const or_maybe_fns = ArrayOrMaybe(IntToFloatFn){ .inr = mul_pi_f64 };

    const array_array_a = ArrayOrMaybeApplicative.fapply(u32, f64, or_array_fns, or_array_a);
    for (&[_]f64{ 4.14, 6.28, 5.71828, 10.87312 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_array_a.inl[i], std.math.floatEps(f64));
    }

    const maybe_array_a = ArrayOrMaybeApplicative.fapply(u32, f64, or_maybe_fns, or_array_a);
    for (&[_]f64{ 3.14, 6.28, 9.42, 12.56 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, maybe_array_a.inl[i], std.math.floatEps(f64));
    }

    const array_maybe_a = ArrayOrMaybeApplicative.fapply(u32, f64, or_array_fns, or_maybe_a);
    for (&[_]f64{ 10.14, 21.98, 9.71828, 19.02796 }, 0..) |a, i| {
        try testing.expectApproxEqRel(a, array_maybe_a.inl[i], std.math.floatEps(f64));
    }

    const maybe_maybe_a = ArrayOrMaybeApplicative.fapply(u32, f64, or_maybe_fns, or_maybe_a);
    try testing.expectEqual(21.98, maybe_maybe_a.inr);
}

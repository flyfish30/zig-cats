const std = @import("std");
const base = @import("../base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");

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

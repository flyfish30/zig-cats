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
        const FunctorF = Functor(ImplF);
        const FunctorG = Functor(ImplG);

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
            return .{
                ImplF.fmap(K, map_fn, fga[0]),
                ImplG.fmap(K, map_fn, fga[1]),
            };
        }

        pub fn fmapLam(
            comptime K: MapFnKind,
            map_lam: anytype,
            fga: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            return .{
                ImplF.fmapLam(K, map_lam, fga[0]),
                ImplG.fmapLam(K, map_lam, fga[1]),
            };
        }
    };
}

pub fn ProductApplicativeImpl(comptime ImplF: type, comptime ImplG: type) type {
    return struct {
        pub const SupImpl = ProductFunctorImpl(ImplF, ImplG);

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
            return .{
                ImplF.pure(a),
                ImplG.pure(a),
            };
        }

        pub fn fapply(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: F(*const fn (A) B),
            fga: F(A),
        ) F(B) {
            return .{
                ImplF.fapply(A, B, fgf[0], fga[0]),
                ImplG.fapply(A, B, fgf[1], fga[1]),
            };
        }

        pub fn fapplyLam(
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            fgf: anytype,
            fga: F(A),
        ) F(B) {
            return .{
                ImplF.fapplyLam(A, B, fgf[0], fga[0]),
                ImplG.fapplyLam(A, B, fgf[1], fga[1]),
            };
        }
    };
}

/// Get a Product Functor from two Functor, the parameter FunctorF and FunctorG
/// are Functor type.
pub fn ProductFunctor(comptime FunctorF: type, comptime FunctorG: type) type {
    const ImplFG = ProductFunctorImpl(FunctorF.InstanceImpl, FunctorG.InstanceImpl);
    return Functor(ImplFG);
}

/// Get a Product Applicative from two Applicative, the parameter
/// ApplicativeF and ApplicativeG are Applicative Functor type.
pub fn ProductApplicative(comptime ApplicativeF: type, comptime ApplicativeG: type) type {
    const ImplFG = ProductApplicativeImpl(ApplicativeF.InstanceImpl, ApplicativeG.InstanceImpl);
    return Applicative(ImplFG);
}

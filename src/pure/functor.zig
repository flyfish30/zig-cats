const std = @import("std");
const base = @import("../base.zig");
const applicative = @import("applicative.zig");

const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const MapFnKind = base.MapFnKind;
const isMapRef = base.isMapRef;

const Maybe = base.Maybe;
const Array = base.Array;

const getDefaultFn = base.getDefaultFn;

pub const MaybeFunctorImpl = applicative.MaybeApplicativeImpl;
pub const ArrayFunctorImpl = applicative.ArrayApplicativeImpl;

pub fn FunctorFxTypes(comptime F: TCtor) type {
    return struct {
        pub fn FaType(comptime K: MapFnKind, comptime MapFn: type) type {
            if (comptime isMapRef(K)) {
                // The fa paramerter of fmap function is also a reference.
                return *F(std.meta.Child(MapFnInType(MapFn)));
            } else {
                return F(MapFnInType(MapFn));
            }
        }

        pub fn FbType(comptime MapFn: type) type {
            return F(MapFnRetType(MapFn));
        }

        pub fn FaLamType(comptime K: MapFnKind, comptime MapLam: type) type {
            if (comptime isMapRef(K)) {
                // The fa paramerter of fmapLam function is also a reference.
                return *F(std.meta.Child(MapLamInType(MapLam)));
            } else {
                return F(MapLamInType(MapLam));
            }
        }

        pub fn FbLamType(comptime MapLam: type) type {
            return F(MapLamRetType(MapLam));
        }
    };
}

/// Functor typeclass like in Haskell.
/// F is Constructor Type of Functor typeclass, such as Maybe, List.
pub fn Functor(comptime FunctorImpl: type) type {
    if (!@hasDecl(FunctorImpl, "F")) {
        @compileError("The Functor instance must has F type!");
    }

    if (!@hasDecl(FunctorImpl, "BaseType")) {
        @compileError("The Functor instance must has type function: BaseType!");
    }

    if (!@hasDecl(FunctorImpl, "deinitFa")) {
        @compileError("The Functor instance must has deinitFa function!");
    }

    // const F = FunctorImpl.F;
    const InstanceType = struct {
        pub const InstanceImpl = FunctorImpl;

        pub const FaType = InstanceImpl.FaType;
        pub const FbType = InstanceImpl.FbType;
        pub const FaLamType = InstanceImpl.FaLamType;
        pub const FbLamType = InstanceImpl.FbLamType;

        /// Typeclass function for map with function
        const FMapType = @TypeOf(struct {
            fn fmapFn(
                comptime K: MapFnKind,
                // f: a -> b, fa: F a
                f: anytype,
                fa: FaType(K, @TypeOf(f)),
            ) FbType(@TypeOf(f)) {
                _ = fa;
            }
        }.fmapFn);

        /// Typeclass function for map with lambda
        const FMapLamType = @TypeOf(struct {
            fn fmapLam(
                comptime K: MapFnKind,
                // f: a -> b, fa: F a
                lam: anytype,
                fa: FaLamType(K, @TypeOf(lam)),
            ) FbLamType(@TypeOf(lam)) {
                _ = fa;
            }
        }.fmapLam);

        pub fn init() void {
            if (@TypeOf(InstanceImpl.fmap) != FMapType) {
                @compileError("Incorrect type of fmap for Functor instance " ++ @typeName(InstanceImpl));
            }
            if (@TypeOf(InstanceImpl.fmapLam) != FMapLamType) {
                @compileError("Incorrect type of fmapLam for Functor instance " ++ @typeName(InstanceImpl));
            }
        }

        pub const fmap = InstanceImpl.fmap;
        pub const fmapLam = InstanceImpl.fmapLam;
    };

    InstanceType.init();
    return InstanceType;
}

pub fn NatTransType(comptime F: TCtor, comptime G: TCtor) type {
    return @TypeOf(struct {
        fn transFn(comptime A: type, fa: F(A)) G(A) {
            _ = fa;
        }
    }.transFn);
}

/// Natural Translation typeclass like in Haskell.
/// F and G is Constructor Type of Functor typeclass, such as Maybe, List.
pub fn NatTrans(
    comptime NatTransImpl: type,
) type {
    if (!(@hasDecl(NatTransImpl, "F") and @hasDecl(NatTransImpl, "G"))) {
        @compileError("The NatTrans instance must has F and G type!");
    }

    const F = NatTransImpl.F;
    const G = NatTransImpl.G;

    const InstanceType = struct {
        pub const InstanceImpl = NatTransImpl;

        const FTransType = @TypeOf(struct {
            fn transFn(comptime A: type, fa: F(A)) G(A) {
                _ = fa;
            }
        }.transFn);

        pub fn init() void {
            if (@TypeOf(InstanceImpl.trans) != FTransType) {
                @compileError("Incorrect type of fmap for NatTrans instance " ++ @typeName(InstanceImpl));
            }
        }

        pub const trans = InstanceImpl.trans;
    };

    InstanceType.init();
    return InstanceType;
}

pub fn MaybeToArrayNatImpl(comptime len: usize) type {
    return struct {
        const F = Maybe;
        const G = Array(len);

        pub fn trans(comptime A: type, fa: F(A)) G(A) {
            if (fa) |a| {
                return [1]A{a} ** len;
            } else {
                const info_a = @typeInfo(A);
                if (info_a == .Fn) {
                    return [1]A{getDefaultFn(A)} ** len;
                } else if (info_a == .Pointer and @typeInfo(std.meta.Child(A)) == .Fn) {
                    return [1]A{getDefaultFn(std.meta.Child(A))} ** len;
                }
                return std.mem.zeroes([len]A);
            }
        }
    };
}

pub fn ArrayToMaybeNatImpl(comptime len: usize) type {
    return struct {
        const F = Array(len);
        const G = Maybe;

        pub fn trans(comptime A: type, fa: F(A)) G(A) {
            return fa[0];
        }
    };
}

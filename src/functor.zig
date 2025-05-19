const std = @import("std");
const base = @import("base.zig");
const applicative = @import("applicative.zig");
const maybe = @import("maybe.zig");
const arraym = @import("array_list_monad.zig");

const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const MapFnKind = base.MapFnKind;
const isMapRef = base.isMapRef;

const Maybe = base.Maybe;
const ArrayList = std.ArrayList;

pub const MaybeFunctorImpl = applicative.MaybeApplicativeImpl;
pub const ArrayListFunctorImpl = applicative.ArrayListApplicativeImpl;

pub fn FunctorFxTypes(comptime F: TCtor, comptime E: ?type) type {
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
            const info = @typeInfo(MapFnRetType(MapFn));
            if (E == null) {
                if (info != .error_union) {
                    return F(MapFnRetType(MapFn));
                }
                return info.error_union.error_set!F(info.error_union.payload);
            }

            const _E = E.?;
            if (info != .error_union) {
                return _E!F(MapFnRetType(MapFn));
            }

            return (_E || info.error_union.error_set)!F(info.error_union.payload);
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
            const info = @typeInfo((MapLamRetType(MapLam)));
            if (E == null) {
                if (info != .error_union) {
                    return F(MapLamRetType(MapLam));
                }
                return info.error_union.error_set!F(info.error_union.payload);
            }

            const _E = E.?;
            if (info != .error_union) {
                return _E!F(MapLamRetType(MapLam));
            }

            return (_E || info.error_union.error_set)!F(info.error_union.payload);
        }
    };
}

/// Functor typeclass like in Haskell.
/// F is Constructor Type of Functor typeclass, such as Maybe, List.
pub fn Functor(comptime F: TCtor) type {
    const FunctorImpl = FunctorImplFromTCtor(F);
    const ImplFVoid = if (@typeInfo(FunctorImpl.F(void)) == .pointer)
        std.meta.Child(FunctorImpl.F(void))
    else
        FunctorImpl.F(void);
    const FVoid = if (@typeInfo(F(void)) == .pointer) std.meta.Child(F(void)) else F(void);
    if (FVoid != ImplFVoid) {
        @compileError("F type=" ++ @typeName(F(void)) ++ ", FunctorImpl.F type=" ++ @typeName(FunctorImpl.F(void)));
    }
    return FunctorFromImpl(FunctorImpl);
}

pub fn FunctorFromImpl(comptime FunctorImpl: type) type {
    if (!@hasDecl(FunctorImpl, "F")) {
        @compileError("The Functor instance must has F type!");
    }

    if (!@hasDecl(FunctorImpl, "BaseType")) {
        @compileError("The Functor instance must has type function: BaseType!");
    }

    if (!@hasDecl(FunctorImpl, "Error")) {
        @compileError("The Functor instance must has Error type!");
    }

    if (!@hasDecl(FunctorImpl, "deinitFa")) {
        @compileError("The Functor instance must has deinitFa function!");
    }

    // const F = FunctorImpl.F;
    const T = struct {
        pub const is_constrait = true;
        const Self = @This();
        pub const InstanceImpl = FunctorImpl;
        pub const Error = InstanceImpl.Error;

        pub const FaType = InstanceImpl.FaType;
        pub const FbType = InstanceImpl.FbType;
        pub const FaLamType = InstanceImpl.FaLamType;
        pub const FbLamType = InstanceImpl.FbLamType;

        /// Typeclass function for map with function
        const FMapType = @TypeOf(struct {
            fn fmapFn(
                instance: *InstanceImpl,
                comptime K: MapFnKind,
                // f: a -> b, fa: F a
                f: anytype,
                fa: FaType(K, @TypeOf(f)),
            ) FbType(@TypeOf(f)) {
                _ = instance;
                _ = fa;
            }
        }.fmapFn);

        /// Typeclass function for map with lambda
        const FMapLamType = @TypeOf(struct {
            fn fmapLam(
                instance: *const InstanceImpl,
                comptime K: MapFnKind,
                // f: a -> b, fa: F a
                lam: anytype, // a lambda with funtion *const fn(Self, A) B
                fa: FaLamType(K, @TypeOf(lam)),
            ) FbLamType(@TypeOf(lam)) {
                _ = instance;
                _ = fa;
            }
        }.fmapLam);
    };

    if (@TypeOf(FunctorImpl.fmap) != T.FMapType) {
        @compileError("Incorrect type of fmap for Functor instance " ++ @typeName(FunctorImpl));
    }
    if (@TypeOf(FunctorImpl.fmapLam) != T.FMapLamType) {
        @compileLog("Functor: Impl.fmapLam type=" ++ @typeName(@TypeOf(FunctorImpl.fmapLam)));
        @compileLog("Functor: T.FMapLamType=" ++ @typeName(T.FMapLamType));
        @compileError("Incorrect type of fmapLam for Functor instance " ++ @typeName(FunctorImpl));
    }
    return base.ConstraitType(T);
}

const functorImplMap = std.StaticStringMap(type).initComptime(.{
    .{ @typeName(Maybe(void)), maybe.MaybeMonadImpl },
    .{ @typeName(ArrayList(void)), arraym.ArrayListMonadImpl },
    // Add more FunctorImply and associated type
});

pub fn FunctorImplFromTCtor(comptime F: TCtor) type {
    comptime {
        const T = F(void);
        switch (@typeInfo(T)) {
            .@"struct", .@"enum", .@"union", .@"opaque" => {
                if (@hasDecl(T, "FunctorImpl")) {
                    return T.FunctorImpl;
                }
            },
            .optional => return maybe.MaybeMonadImpl,
            .pointer => return std.meta.Child(T).FunctorImpl,
            else => {},
        }

        const impl = functorImplMap.get(@typeName(T));
        if (impl == null) {
            @compileError("The customered Functor(" ++ @typeName(T) ++ ") must has FunctorImpl!");
        }
        return impl.?;
    }
}

pub fn NatGxTypes(comptime G: TCtor, comptime E: ?type) type {
    return struct {
        fn GaType(comptime A: type) type {
            return if (E == null) G(A) else E.?!G(A);
        }
    };
}

/// Natural Transformation typeclass like in Haskell.
/// F and G is Constructor Type of Functor typeclass, such as Maybe, List.
pub fn NatTrans(
    comptime NatTransImpl: type,
) type {
    if (!(@hasDecl(NatTransImpl, "F") and @hasDecl(NatTransImpl, "G"))) {
        @compileError("The NatTrans instance must has F and G type!");
    }

    if (!(@hasDecl(NatTransImpl, "Error"))) {
        @compileError("The NatTrans instance must has Error type!");
    }

    const F = NatTransImpl.F;
    _ = Functor(F);
    const G = NatTransImpl.G;
    _ = Functor(G);
    const Error = NatTransImpl.Error;

    const T = struct {
        pub const is_constrait = true;
        const Self = @This();
        pub const InstanceImpl = NatTransImpl;

        const NatTransType = @TypeOf(struct {
            fn transFn(
                instance: InstanceImpl,
                comptime A: type,
                fa: F(A),
            ) Error!G(A) {
                _ = instance;
                _ = fa;
            }
        }.transFn);
    };

    if (@TypeOf(NatTransImpl.trans) != T.NatTransType) {
        @compileLog("Impl trans type: " ++ @typeName(@TypeOf(NatTransImpl.trans)));
        @compileLog("NatTransType: " ++ @typeName(T.NatTransType));
        @compileError("Incorrect type of trans for NatTrans instance: " ++ @typeName(NatTransImpl));
    }
    return base.ConstraitType(T);
}

pub const MaybeToArrayListNatImpl = struct {
    instanceArray: ArrayListFunctorImpl,

    const Self = @This();

    pub const F = Maybe;
    pub const G = ArrayList;
    pub const Error = Functor(G).Error;

    const GaType = NatGxTypes(G, Error).GaType;

    pub fn trans(self: Self, comptime A: type, fa: F(A)) GaType(A) {
        if (fa) |a| {
            var array = try ArrayList(A).initCapacity(self.instanceArray.allocator, 1);
            array.appendAssumeCapacity(a);
            return array;
        } else {
            // return empty ArrayList
            return ArrayList(A).init(self.instanceArray.allocator);
        }
    }
};

pub const ArrayListToMaybeNatImpl = struct {
    const Self = @This();

    pub const F = ArrayList;
    pub const G = Maybe;
    pub const Error = Functor(G).Error;

    const GaType = NatGxTypes(G, Error).GaType;

    pub fn trans(self: Self, comptime A: type, fa: F(A)) GaType(A) {
        _ = self;
        if (fa.items.len > 0) {
            return fa.items[0];
        }

        return null;
    }
};

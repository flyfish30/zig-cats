const std = @import("std");
const base = @import("../base.zig");
const functor = @import("functor.zig");
const monad = @import("monad.zig");

const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const isErrorUnionOrVal = base.isErrorUnionOrVal;

const Functor = functor.Functor;

pub const MaybeApplicativeImpl = monad.MaybeMonadImpl;
pub const ArrayApplicativeImpl = monad.ArrayMonadImpl;

/// Applicative Functor typeclass like in Haskell, it inherit from Functor.
/// F is instance of Applicative Functor typeclass, such as Maybe, List
pub fn Applicative(comptime ApplicativeImpl: type) type {
    const F = ApplicativeImpl.F;
    const has_sup_impl = @hasField(ApplicativeImpl, "SupImpl");

    const InstanceType = struct {
        pub const InstanceImpl = ApplicativeImpl;
        const FunctorSup = if (has_sup_impl)
            Functor(InstanceImpl.SupImpl)
        else
            Functor(InstanceImpl);

        const PureType = @TypeOf(struct {
            fn pureFn(a: anytype) F(@TypeOf(a)) {}
        }.pureFn);

        const ApplyType = @TypeOf(struct {
            fn fapplyFn(
                comptime A: type,
                comptime B: type,
                // applicative function: F (a -> b), fa: F a
                ff: F(*const fn (A) B),
                fa: F(A),
            ) F(B) {
                _ = ff;
                _ = fa;
            }
        }.fapplyFn);

        const ApplyLamType = @TypeOf(struct {
            fn fapplyLam(
                comptime A: type,
                comptime B: type,
                // applicative function: F (a -> b), fa: F a
                flam: anytype, // a F(lambda) that present F(*const fn (A) B),
                fa: F(A),
            ) F(B) {
                _ = flam;
                _ = fa;
            }
        }.fapplyLam);

        // pub fn liftA2(
        //     // map2 function f: a -> b -> c
        //     f: anytype,
        //     fa: Map2FaType(@TypeOf(f)),
        //     fb: Map2FbType(@TypeOf(f)),
        // ) Map2FcType(@TypeOf(f)) {
        //     // liftA2 f fa fb = pure f <*> fa <*> fb
        // }

        pub fn init() void {
            if (@TypeOf(InstanceImpl.pure) != PureType) {
                @compileError("Incorrect type of pure for Applicative instance " ++ @typeName(InstanceImpl));
            }
            if (@TypeOf(InstanceImpl.fapply) != ApplyType) {
                @compileError("Incorrect type of fapply for Applicative instance " ++ @typeName(InstanceImpl));
            }
            if (@TypeOf(InstanceImpl.fapplyLam) != ApplyLamType) {
                @compileError("Incorrect type of fapply lambda for Applicative instance " ++ @typeName(InstanceImpl));
            }
        }

        pub const fmap = FunctorSup.fmap;
        pub const fmapLam = FunctorSup.fmapLam;
        pub const pure = InstanceImpl.pure;
        pub const fapply = InstanceImpl.fapply;
        pub const fapplyLam = InstanceImpl.fapplyLam;
    };

    InstanceType.init();
    return InstanceType;
}

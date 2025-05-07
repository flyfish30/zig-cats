const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const monad = @import("monad.zig");
const maybe = @import("maybe.zig");
const listm = @import("array_list_monad.zig");

const TCtor = base.TCtor;
const isErrorUnionOrVal = base.isErrorUnionOrVal;

const Functor = functor.Functor;

pub const MaybeApplicativeImpl = maybe.MaybeMonadImpl;
pub const ArrayListApplicativeImpl = listm.ArrayListMonadImpl;

pub fn ApplicativeFxTypes(comptime F: TCtor, comptime E: type) type {
    return struct {
        /// return type of pure a
        pub fn APaType(comptime A: type) type {
            const has_err, const _A = comptime isErrorUnionOrVal(A);
            if (has_err) {
                return (E || @typeInfo(A).error_union.error_set)!F(_A);
            } else {
                return E!F(A);
            }
        }

        /// return type of fapply
        pub fn AFbType(comptime B: type) type {
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            if (has_err) {
                return (E || @typeInfo(B).error_union.error_set)!F(_B);
            } else {
                return E!F(B);
            }
        }
    };
}

/// Applicative Functor typeclass like in Haskell, it inherit from Functor.
/// F is instance of Applicative Functor typeclass, such as Maybe, List
pub fn Applicative(comptime ApplicativeImpl: type) type {
    const F = ApplicativeImpl.F;
    const has_sup_impl = @hasField(ApplicativeImpl, "functor_sup");

    return struct {
        const Self = @This();
        pub const InstanceImpl = ApplicativeImpl;
        const FunctorSup = if (has_sup_impl)
            Functor(InstanceImpl.SupImpl)
        else
            Functor(InstanceImpl);

        pub const Error = InstanceImpl.Error;
        pub const APaType = InstanceImpl.APaType;
        pub const AFbType = InstanceImpl.AFbType;

        const PureType = @TypeOf(struct {
            fn pureFn(instance: *InstanceImpl, a: anytype) APaType(@TypeOf(a)) {
                _ = instance;
            }
        }.pureFn);

        const ApplyType = @TypeOf(struct {
            fn fapplyFn(
                instance: *InstanceImpl,
                comptime A: type,
                comptime B: type,
                // applicative function: F (a -> b), fa: F a
                ff: F(*const fn (A) B),
                fa: F(A),
            ) AFbType(B) {
                _ = instance;
                _ = ff;
                _ = fa;
            }
        }.fapplyFn);

        const ApplyLamType = @TypeOf(struct {
            fn fapplyLam(
                instance: *InstanceImpl,
                comptime A: type,
                comptime B: type,
                // applicative function: F (a -> b), fa: F a
                flam: anytype, // a F(lambda) with funtion F(*const fn (Self, A) B),
                fa: F(A),
            ) AFbType(B) {
                _ = instance;
                _ = flam;
                _ = fa;
            }
        }.fapplyLam);

        // pub fn liftA2(
        //     instance: InstanceImpl,
        //     // map2 function f: a -> b -> c
        //     f: anytype,
        //     fa: Map2FaType(@TypeOf(f)),
        //     fb: Map2FbType(@TypeOf(f)),
        // ) Map2FcType(@TypeOf(f)) {
        //     // liftA2 f fa fb = pure f <*> fa <*> fb
        // }

        pub fn init(instance: InstanceImpl) InstanceImpl {
            var inst: InstanceImpl = undefined;

            if (has_sup_impl) {
                const sup = FunctorSup.init(instance.functor_sup);
                inst = instance;
                inst.functor_sup = sup;
            } else {
                inst = FunctorSup.init(instance);
            }

            if (@TypeOf(InstanceImpl.pure) != PureType) {
                @compileError("Incorrect type of pure for Applicative instance " ++ @typeName(InstanceImpl));
            }
            if (@TypeOf(InstanceImpl.fapply) != ApplyType) {
                @compileError("Incorrect type of fapply for Applicative instance " ++ @typeName(InstanceImpl));
            }
            if (@TypeOf(InstanceImpl.fapplyLam) != ApplyLamType) {
                @compileError("Incorrect type of fapply lambda for Applicative instance " ++ @typeName(InstanceImpl));
            }
            return inst;
        }
    };
}

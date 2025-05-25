const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const monad = @import("monad.zig");
const maybe = @import("maybe.zig");
const arraym = @import("array_monad.zig");
const arraylm = @import("array_list_monad.zig");

const TCtor = base.TCtor;
const isErrorUnionOrVal = base.isErrorUnionOrVal;

const Functor = functor.Functor;

const Maybe = base.Maybe;
const ArrayList = std.ArrayList;

pub const MaybeApplicativeImpl = maybe.MaybeMonadImpl;
pub const ArrayListApplicativeImpl = arraylm.ArrayListMonadImpl;

pub fn ApplicativeFxTypes(comptime F: TCtor, comptime E: ?type) type {
    return struct {
        /// return type of pure a
        pub fn APaType(comptime A: type) type {
            const has_err, const _A = comptime isErrorUnionOrVal(A);
            if (E == null) {
                if (has_err)
                    return @typeInfo(A).error_union.error_set!F(_A);
                return F(A);
            }

            if (has_err) {
                return (E.? || @typeInfo(A).error_union.error_set)!F(_A);
            } else {
                return E.?!F(A);
            }
        }

        /// return type of fapply
        pub fn AFbType(comptime B: type) type {
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            if (E == null) {
                if (has_err)
                    return @typeInfo(B).error_union.error_set!F(_B);
                return F(B);
            }

            if (has_err) {
                return (E.? || @typeInfo(B).error_union.error_set)!F(_B);
            } else {
                return E.?!F(B);
            }
        }
    };
}

/// Applicative Functor typeclass like in Haskell, it inherit from Functor.
/// F is instance of Applicative Functor typeclass, such as Maybe, List
pub fn Applicative(comptime F: TCtor) type {
    const ApplicativeImpl = ApplicativeImplFromTCtor(F);
    const ImplFVoid = if (@typeInfo(ApplicativeImpl.F(void)) == .pointer)
        std.meta.Child(ApplicativeImpl.F(void))
    else
        ApplicativeImpl.F(void);
    const FVoid = if (@typeInfo(F(void)) == .pointer) std.meta.Child(F(void)) else F(void);
    if (FVoid != ImplFVoid) {
        @compileError("F type=" ++ @typeName(F(void)) ++ ", ApplicativeImpl.F type=" ++ @typeName(ApplicativeImpl.F(void)));
    }
    return ApplicativeFromImpl(ApplicativeImpl);
}

pub fn ApplicativeFromImpl(comptime ApplicativeImpl: type) type {
    _ = functor.FunctorFromImpl(ApplicativeImpl);
    const T = struct {
        pub const is_constrait = true;
        const Self = @This();
        const F = ApplicativeImpl.F;
        pub const InstanceImpl = ApplicativeImpl;

        pub const Error = InstanceImpl.Error;
        pub const APaType = InstanceImpl.APaType;
        pub const AFbType = InstanceImpl.AFbType;

        const PureType = @TypeOf(struct {
            fn pureFn(instance: *const InstanceImpl, a: anytype) APaType(@TypeOf(a)) {
                _ = instance;
            }
        }.pureFn);

        const ApplyType = @TypeOf(struct {
            fn fapplyFn(
                instance: *const InstanceImpl,
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
                instance: *const InstanceImpl,
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
    };

    if (@TypeOf(ApplicativeImpl.pure) != T.PureType) {
        @compileError("Incorrect type of pure for Applicative instance " ++ @typeName(ApplicativeImpl));
    }
    if (@TypeOf(ApplicativeImpl.fapply) != T.ApplyType) {
        @compileError("Incorrect type of fapply for Applicative instance " ++ @typeName(ApplicativeImpl));
    }
    if (@TypeOf(ApplicativeImpl.fapplyLam) != T.ApplyLamType) {
        @compileError("Incorrect type of fapply lambda for Applicative instance " ++ @typeName(ApplicativeImpl));
    }
    return base.ConstraitType(T);
}

const applicativeImplMap = std.StaticStringMap(type).initComptime(.{
    .{ @typeName(Maybe(void)), maybe.MaybeMonadImpl },
    .{ @typeName(ArrayList(void)), arraylm.ArrayListMonadImpl },
    // Add more ApplicativeImply and associated type
});

pub fn ApplicativeImplFromTCtor(comptime F: TCtor) type {
    comptime {
        const T = F(void);
        switch (@typeInfo(T)) {
            .@"struct", .@"enum", .@"union", .@"opaque" => {
                if (@hasDecl(T, "ApplicativeImpl")) {
                    return T.ApplicativeImpl;
                }
            },
            .optional => return maybe.MaybeMonadImpl,
            .array => |info| return arraym.ArrayMonadImpl(info.len),
            .pointer => return std.meta.Child(T).ApplicativeImpl,
            else => {},
        }

        const impl = applicativeImplMap.get(@typeName(T));
        if (impl == null) {
            @compileError("The customered Functor(" ++ @typeName(T) ++ ") must has ApplicativeImpl!");
        }
        return impl.?;
    }
}

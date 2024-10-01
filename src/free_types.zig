//! Define some types to implement Free Structure in Haskell, such as Free Monad,
//! Free Applicative, etc.

const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const arraym = @import("array_list_monad.zig");
const testu = @import("test_utils.zig");

const testing = std.testing;
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Maybe = base.Maybe;
const ArrayList = std.ArrayList;

const TCtor = base.TCtor;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const FMapMode = base.FMapMode;
const MapFnKind = base.MapFnKind;
const isMapRef = base.isMapRef;
const isInplaceMap = base.isInplaceMap;
const isErrorUnionOrVal = base.isErrorUnionOrVal;

const Functor = functor.Functor;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;
const ArrayListMonadImpl = arraym.ArrayListMonadImpl;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

const DEFAULT_LEN: usize = 8;

/// This is type constructor of Free Monad, the parameter F must be a Functor,
/// and all value constructors of F must take only one parameter.
/// If you need a value constructor with multiple parameters, you can curry it
/// into multiple value constructors taht take one parameter.
pub fn FreeMonad(comptime F: TCtor, comptime A: type) type {
    return FreeM(F)(A);
}

// TODO: FreeM first parameter is TyFunctor, that has two constructor: TCtor and ValCtor

/// The type function FreeM is currying form of type constructor FreeMonad.
pub fn FreeM(comptime F: TCtor) TCtor {
    return struct {
        fn FreeF(comptime A: type) type {
            return union(enum) {
                // The FreeMonad(F, A) type that defined by Haskell is
                // data Free f a = Pure a
                //               | Free (f (Free f a)
                // The value Free (f2 (Free (f1 (Free (f0 pure_m))))) layout is
                // ( pure_m, [f0, f1, f2] )

                // pure value of FreeMonad(F, A)
                pure_m: A,
                // tuple of (pure FreeMonad(F, A), reversed f list)
                free_m: struct { *Self, ArrayList(ValCtor) },

                const Self = @This();
                const BaseType = A;

                // the value constructor function for F
                // index of Constructor functions
                pub const ValCtor = u16;
                const f_val_ctors = GetValCtors(A, MaybeCtorDefs);

                pub fn deinit(self: Self) void {
                    if (self == .free_m) {
                        const allocator = self.free_m[1].allocator;
                        self.free_m[1].deinit();
                        allocator.destroy(self.free_m[0]);
                    }
                }

                pub inline fn pureM(a: A) Self {
                    return Self{ .pure_m = a };
                }

                pub inline fn freeM(allocator: Allocator, a: A, fs: []ValCtor) !Self {
                    const new_pure_m = try allocator.create(Self);
                    new_pure_m.* = .{ .pure_m = a };
                    var flist = try ArrayList(ValCtor).initCapacity(allocator, fs.len);
                    flist.appendSliceAssumeCapacity(fs);
                    return .{ .free_m = .{ new_pure_m, flist } };
                }

                // This function has move semantics, all value in self move to new self.
                pub fn appendValFn(self: Self, allocator: Allocator, f: ValCtor) !Self {
                    if (self == .pure_m) {
                        var flist = try ArrayList(ValCtor).initCapacity(allocator, DEFAULT_LEN);
                        flist.appendAssumeCapacity(f);
                        var new_pure_m = try allocator.create(Self);
                        new_pure_m.pure_m = self.pure_m;
                        return .{ .free_m = .{ new_pure_m, flist } };
                    } else {
                        var flist = self.free_m[1];
                        try flist.append(f);
                        return .{ .free_m = .{ self.free_m[0], flist } };
                    }
                }

                // This function has move semantics, all value in self move to new self.
                pub fn appendValFns(self: Self, allocator: Allocator, fs: []ValCtor) !Self {
                    if (self == .pure_m) {
                        var flist = try ArrayList(ValCtor).initCapacity(allocator, fs.len);
                        flist.appendSliceAssumeCapacity(fs);
                        const new_pure_m = try allocator.create(Self);
                        new_pure_m.* = .{ .pure_m = self.pure_m };
                        return .{ .free_m = .{ new_pure_m, flist } };
                    } else {
                        var flist = self.free_m[1];
                        try flist.appendSlice(fs);
                        return .{ .free_m = .{ self.free_m[0], flist } };
                    }
                }

                pub fn foldFree(self: Self, f: *const fn (F(A)) A) A {
                    if (self == .pure_m) {
                        return self.pure_m;
                    }

                    var acc_a = self.free_m[0].pure_m;
                    for (self.free_m[1].items) |ctor_idx| {
                        const val_ctor_info = f_val_ctors[ctor_idx];
                        const fa = val_ctor_info.callValCtorFn(@constCast(&[_]A{acc_a}));
                        acc_a = f(fa);
                    }
                    return acc_a;
                }
            };
        }
    }.FreeF;
}

fn ValCtorsType(comptime A: type, comptime DefsFn: *const fn (comptime type) type) type {
    const ValCtorDefs = DefsFn(A);
    const CtorEnum = std.meta.DeclEnum(ValCtorDefs);
    const enum_fields = std.meta.fields(CtorEnum);
    return [enum_fields.len]ValCtorInfo(A, CtorEnum, DefsFn(A));
}

fn ValCtorInfo(
    comptime A: type,
    comptime ValCtorE: type,
    comptime DefsFn: type,
) type {
    const first_e = @as(ValCtorE, @enumFromInt(0));
    const first_ctor_fn = @field(DefsFn, @tagName(first_e));
    const fn_info = @typeInfo(std.meta.Child(@TypeOf(first_ctor_fn)));
    const ValCtorRetType = fn_info.Fn.return_type.?;
    return struct {
        ctor_e: ValCtorE,
        params_len: u8,

        const Self = @This();
        pub fn callValCtorFn(self: Self, as: []A) ValCtorRetType {
            switch (self.ctor_e) {
                inline else => |e| {
                    std.debug.print("ValCtor enum: {any}\n", .{e});
                    std.debug.print(
                        "as.len = {d}, params_len = {d}\n",
                        .{ as.len, self.params_len },
                    );
                    if (self.params_len > 0) {
                        std.debug.assert(as.len == self.params_len);
                    } else {
                        std.debug.assert(as.len == 1);
                    }
                    const ctor_fn = @field(DefsFn, @tagName(e));
                    const Args = std.meta.ArgsTuple(std.meta.Child(@TypeOf(ctor_fn)));
                    var args: Args = undefined;
                    comptime var i = 0;
                    inline while (i < @typeInfo(Args).Struct.fields.len) : (i += 1) {
                        args[i] = as[i];
                    }
                    return @call(.auto, ctor_fn, args);
                },
            }
        }
    };
}

pub fn GetValCtors(
    comptime A: type,
    comptime DefsFn: *const fn (comptime type) type,
) ValCtorsType(A, DefsFn) {
    const ValCtorDefs = DefsFn(A);
    const CtorEnum = std.meta.DeclEnum(ValCtorDefs);
    const enum_fields = std.meta.fields(CtorEnum);

    //     const ValCtors = ValCtorsType(A, DefsFn);
    var val_ctors: [enum_fields.len]ValCtorInfo(A, CtorEnum, DefsFn(A)) = undefined;
    inline for (enum_fields, 0..) |field, i| {
        const name = field.name;
        const ctor_fn = @field(ValCtorDefs, name);
        const fn_info = @typeInfo(std.meta.Child(@TypeOf(ctor_fn)));
        const params_len = fn_info.Fn.params.len;
        const ctor_e = @as(CtorEnum, @enumFromInt(i));
        val_ctors[i].ctor_e = ctor_e;
        val_ctors[i].params_len = params_len;
    }
    return val_ctors;
}

/// All value constructors for Maybe Functor
fn MaybeCtorDefs(comptime A: type) type {
    return struct {
        pub const Nothing: *const fn () Maybe(A) = nothingFn;
        pub const Just: *const fn (A) Maybe(A) = justFn;

        // Value constructor functions for Maybe
        fn nothingFn() Maybe(A) {
            return null;
        }

        fn justFn(a: A) Maybe(A) {
            return a;
        }
    };
}

fn foldMaybe(comptime A: type) *const fn (a: Maybe(A)) A {
    return struct {
        fn foldFn(a: Maybe(A)) A {
            return a orelse 0;
        }
    }.foldFn;
}

test "FreeMonad(F, A) constructor functions and foldFree" {
    const allocator = testing.allocator;

    var a: u32 = 42;
    _ = &a;
    const pure_freem = FreeMonad(Maybe, u32).pureM(a);
    try testing.expectEqual(42, pure_freem.pure_m);

    const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
    const Nothing: u16 = @intFromEnum(MaybeCtorEnum.Nothing);
    const Just: u16 = @intFromEnum(MaybeCtorEnum.Just);
    const ValCtor = comptime FreeMonad(Maybe, u32).ValCtor;
    const just_fns = &[_]ValCtor{Just};
    const free_maybe = try FreeMonad(Maybe, u32).freeM(allocator, 42, @constCast(just_fns));
    try testing.expectEqual(42, free_maybe.foldFree(foldMaybe(u32)));

    const free_maybe1 = try free_maybe.appendValFn(allocator, Just);
    try testing.expectEqual(42, free_maybe1.foldFree(foldMaybe(u32)));

    const just_fns3 = &[_]ValCtor{ Just, Nothing, Just };
    const free_maybe2 = try free_maybe1.appendValFns(allocator, @constCast(just_fns3));
    defer free_maybe2.deinit();
    try testing.expectEqual(0, free_maybe2.foldFree(foldMaybe(u32)));
}

/// The Monad instance of FreeMonad, the parameter FunF is a Functor.
pub fn FreeMonadImpl(comptime FunF: TCtor) type {
    return struct {
        allocator: Allocator,

        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = FreeM(FunF);

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime FreeT: type) type {
            return FreeT.BaseType;
        }

        pub const Error = Allocator.Error;

        pub const FxTypes = FunctorFxTypes(F, Error);
        pub const FaType = FxTypes.FaType;
        pub const FbType = FxTypes.FbType;
        pub const FaLamType = FxTypes.FaLamType;
        pub const FbLamType = FxTypes.FbLamType;

        const AFxTypes = ApplicativeFxTypes(F, Error);
        pub const APaType = AFxTypes.APaType;
        pub const AFbType = AFxTypes.AFbType;

        pub const MbType = MonadFxTypes(F, Error).MbType;

        pub fn deinitFa(
            fa: anytype, // FreeMonad(F, A)
            comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
        ) void {
            if (fa == .pure_m) {
                free_fn(fa.pure_m);
            } else {
                free_fn(fa.free_m[0].pure_m);
                const allocator = fa.free_m[2];
                allocator.destroy(fa.free_m[0]);
                fa.free_m[1].deinit();
            }
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            // const A = MapFnInType(@TypeOf(map_fn));
            const B = MapFnRetType(@TypeOf(map_fn));
            const has_err, const _B = comptime isErrorUnionOrVal(B);

            const is_pure, const b = if (comptime isMapRef(K)) blk_t: {
                const is_pure = fa.* == .pure_m;
                const p_a = if (is_pure) &fa.pure_m else &fa.free_m[0].pure_m;
                break :blk_t .{ is_pure, map_fn(p_a) };
            } else blk_f: {
                const is_pure = fa == .pure_m;
                const a = if (is_pure) fa.pure_m else fa.free_m[0].pure_m;
                break :blk_f .{ is_pure, map_fn(a) };
            };
            const _b = if (has_err) try b else b;
            if (is_pure) {
                return .{ .pure_m = _b };
            } else {
                const new_pure_m = try self.allocator.create(FreeMonad(FunF, _B));
                new_pure_m.* = .{ .pure_m = _b };
                return .{ .free_m = .{ new_pure_m, try fa.free_m[1].clone() } };
            }
        }

        pub fn fmapLam(
            self: *Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            const B = MapLamRetType(@TypeOf(map_lam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);

            const is_pure, const b = if (comptime isMapRef(K)) blk_t: {
                const is_pure = fa.* == .pure_m;
                const p_a = if (is_pure) &fa.pure_m else &fa.free_m[0].pure_m;
                break :blk_t .{ is_pure, map_lam.call(p_a) };
            } else blk_f: {
                const is_pure = fa == .pure_m;
                const a = if (is_pure) fa.pure_m else fa.free_m[0].pure_m;
                break :blk_f .{ is_pure, map_lam.call(a) };
            };
            const _b = if (has_err) try b else b;
            if (is_pure) {
                return .{ .pure_m = _b };
            } else {
                const new_pure_m = try self.allocator.create(FreeMonad(FunF, _B));
                new_pure_m.* = .{ .pure_m = _b };
                return .{ .free_m = .{ new_pure_m, try fa.free_m[1].clone() } };
            }
        }

        pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
            _ = self;
            const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
            const _a: _A = if (has_err) try a else a;
            return .{ .pure_m = _a };
        }

        pub fn fapply(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            ff: F(*const fn (A) B),
            fa: F(A),
        ) AFbType(B) {
            const has_err, const _B = comptime isErrorUnionOrVal(B);

            if (ff == .pure_m) {
                return self.fmap(.NewValMap, ff.pure_m, fa);
            }

            const map_fn = ff.free_m[0].pure_m;
            if (fa == .pure_m) {
                const b = map_fn(fa.pure_m);
                const _b: _B = if (has_err) try b else b;
                const new_pure_m = try self.allocator.create(Self);
                new_pure_m.* = .{ .pure_m = _b };
                return .{ .free_m = .{ new_pure_m, try ff.free_m[1].clone() } };
            } else {
                const b = map_fn(fa.free_m[0].pure_m);
                const _b: _B = if (has_err) try b else b;
                const new_pure_m = try self.allocator.create(Self);
                new_pure_m.* = .{ .pure_m = _b };
                const len = fa.free_m[1].items.len + ff.free_m[1].items.len;
                var flist = try @TypeOf(fa.free_m[1]).initCapacity(self.allocator, len);
                flist.appendSliceAssumeCapacity(fa.free_m[1].items);
                flist.appendSliceAssumeCapacity(ff.free_m[1].items);
                return .{ .free_m = .{ new_pure_m, flist } };
            }
        }

        pub fn fapplyLam(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(A),
        ) AFbType(B) {
            const has_err, const _B = comptime isErrorUnionOrVal(B);

            if (flam == .pure_m) {
                return self.fmap(.NewValMap, flam.pure_m, fa);
            }

            const map_lam = flam.free_m[0].pure_m;
            if (fa == .pure_m) {
                const b = map_lam.call(fa.pure_m);
                const _b: _B = if (has_err) try b else b;
                const new_pure_m = try self.allocator.create(Self);
                new_pure_m.* = .{ .pure_m = _b };
                return .{ .free_m = .{ new_pure_m, flam.free_m[1] } };
            } else {
                const b = map_lam.call(fa.free_m[0].pure_m);
                const _b: _B = if (has_err) try b else b;
                const new_pure_m = try self.allocator.create(Self);
                new_pure_m.* = .{ .pure_m = _b };
                const len = fa.free_m[1].items.len + flam.free_m[1].items.len;
                var flist = try @TypeOf(fa.free_m[1]).initCapacity(self.allocator, len);
                flist.appendSliceAssumeCapacity(fa.free_m[1].items);
                flist.appendSliceAssumeCapacity(flam.free_m[1].items);
                return .{ .free_m = .{ new_pure_m, flist } };
            }
        }
        pub fn bind(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*Self, A) MbType(B),
        ) MbType(B) {
            if (ma == .pure_m) {
                return k(ma.pure_m);
            }

            const freem = k(ma.free_m[0].pure);
            if (freem == .pure_m) {
                const new_pure_m = try self.allocator.create(Self);
                new_pure_m.* = .{ .pure_m = freem.pure_m };
                return .{ .free_m = .{ new_pure_m, ma.free_m[1] } };
            } else {
                const new_pure_m = try self.allocator.create(Self);
                new_pure_m.* = .{ .pure_m = freem[0].pure_m };
                const flist = try freem.free_m[1].appendSlices(ma.free_m[1].items);
                return .{ .free_m = .{ new_pure_m, flist } };
            }
        }
    };
}

// These functions are defined for unit test
const add10 = testu.add10;
const add_pi_f64 = testu.add_pi_f64;
const mul_pi_f64 = testu.mul_pi_f64;

const Add_x_f64_Lam = testu.Add_x_f64_Lam;

test "FreeMonad(F, A) fmap" {
    const allocator = testing.allocator;
    const FreeMFunctor = Functor(FreeMonadImpl(Maybe));
    var freem_functor = FreeMFunctor.init(.{ .allocator = allocator });
    _ = &freem_functor;

    var a: u32 = 42;
    _ = &a;
    // const pure_freem = .{ .pure_m = a };
    const pure_freem = FreeMonad(Maybe, u32).pureM(@as(u32, 42));
    const pure_freem1 = try freem_functor.fmap(.NewValMap, add_pi_f64, pure_freem);
    try testing.expectEqual(45.14, pure_freem1.foldFree(foldMaybe(f64)));

    const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
    // const Nothing: u16 = @intFromEnum(MaybeCtorEnum.Nothing);
    const Just: u16 = @intFromEnum(MaybeCtorEnum.Just);
    const ValCtor = comptime FreeMonad(Maybe, u32).ValCtor;
    const just_fns2 = &[_]ValCtor{ Just, Just };
    const free_maybe = try pure_freem.appendValFns(allocator, @constCast(just_fns2));
    defer free_maybe.deinit();
    const free_maybe1 = try freem_functor.fmap(.NewValMap, add10, free_maybe);
    defer free_maybe1.deinit();
    try testing.expectEqual(52, free_maybe1.foldFree(foldMaybe(u32)));

    const add_x_f64_lam = Add_x_f64_Lam{ ._x = 3.14 };
    const free_maybe2 = try freem_functor.fmapLam(.NewValMap, add_x_f64_lam, free_maybe1);
    defer free_maybe2.deinit();
    try testing.expectEqual(55.14, free_maybe2.foldFree(foldMaybe(f64)));
}

fn ListF(comptime A: type) type {
    return struct {
        fn ListAX(comptime X: type) type {
            return union(enum) {
                nilF: X,
                consF: struct { A, X },

                const Self = @This();
            };
        }
    }.ListAX;
}

fn ListFCtorDefs(comptime X: type) type {
    return struct {
        pub const NilF: *const fn () ListF(X) = nilFn;
        pub const ConsF: *const fn (X) ListF(X) = consFn;

        // Value constructor functions for Maybe
        fn nilFn() Maybe(X) {
            return null;
        }

        fn consFn(x: X) Maybe(X) {
            return x;
        }
    };
}

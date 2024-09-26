//! Definition State struct, these is a instance of Functor|Applicative|Monad typeclass.

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

const TransCtxKind = enum(u8) {
    NormalTrans,
    ConstantTrans,
    PutTrans,
    FmapTrans,
    PureTrans,
    FapplyTrans,
    BindTrans,
};

const TransCtxInfo = struct {
    ctx_size: CtxSizeType,
    ctx_kind: TransCtxKind,
    ctx_align: CtxAlignType,

    const CtxSizeType = u16;
    const CtxAlignType = u8;
};

fn mkTransCtxInfo(comptime Ctx: type, comptime K: TransCtxKind) TransCtxInfo {
    comptime assert(@sizeOf(Ctx) < std.math.maxInt(TransCtxInfo.CtxSizeType));
    comptime assert(@alignOf(Ctx) < std.math.maxInt(TransCtxInfo.CtxAlignType));
    return .{ .ctx_size = @sizeOf(Ctx), .ctx_kind = K, .ctx_align = @alignOf(Ctx) };
}

pub fn StateContext(comptime cfg: anytype) type {
    return struct {
        pub const ctx_cfg = cfg;
        const Error = ctx_cfg.error_set;

        // the currying function of State function
        pub fn StateCurrying(comptime S: type) TCtor {
            return struct {
                fn StateF(comptime A: type) type {
                    return struct {
                        // translate action lambda for State
                        trans_lam: TransLam,
                        trans_info: TransCtxInfo,

                        const Self = @This();
                        pub const StateS = S;
                        pub const StateA = A;
                        pub const TransLam = struct {
                            trans_ctx: ?*anyopaque = null,
                            trans_fn: *const fn (self: *TransLam, s: S) RetType,

                            const RetType = Error!struct { A, S };
                            // translate action function for State
                            pub inline fn call(trans_lam: *TransLam, s: S) RetType {
                                return trans_lam.trans_fn(trans_lam, s);
                            }
                        };
                        pub const free_s = ctx_cfg.free_s;

                        pub fn deinit(state_self: *Self) void {
                            const trans_info = state_self.trans_info;
                            if (state_self.trans_lam.trans_ctx) |trans_ctx| {
                                const len = trans_info.ctx_size;
                                const aligns = comptime [_]u8{ 1, 2, 4, 8, 16, 32, 64, 128 };
                                inline for (aligns) |a| {
                                    if (trans_info.ctx_align == a) {
                                        const slice: []align(a) u8 = @as(
                                            [*]align(a) u8,
                                            @alignCast(@ptrCast(trans_ctx)),
                                        )[0..len];
                                        ctx_cfg.allocator.free(slice);
                                        break;
                                    }
                                } else {
                                    @panic("The alignment of struct TransCtx must is 1, 2, 4, 8, 16, 32, 64, 128\n");
                                }
                            }
                            state_self.trans_info = mkTransCtxInfo(void, .NormalTrans);
                        }

                        pub inline fn runState(state_self: *Self, s: S) Error!struct { A, S } {
                            const trans_lam = state_self.trans_lam;
                            return @constCast(&trans_lam).call(s);
                        }

                        pub inline fn evalState(state_self: *Self, s: S) Error!A {
                            return (try state_self.runState(s))[0];
                        }

                        pub inline fn execState(state_self: *Self, s: S) Error!S {
                            return (try state_self.runState(s))[1];
                        }
                    };
                }
            }.StateF;
        }

        pub fn State(comptime S: type, comptime A: type) type {
            return StateCurrying(S)(A);
        }

        pub fn mkConstantState(comptime S: type, comptime A: type, s: S, a: A) State(S, A) {
            const TransCtx = struct {
                local_s: S,
                local_a: a,
            };

            const trans_fn = struct {
                const RetType = Error!struct { A, S };
                fn f(trans_lam: *State(S, A).TransLam, input_s: S) RetType {
                    ctx_cfg.free_s(ctx_cfg.allocator, input_s);
                    const trans_ctx: *TransCtx = @alignCast(@ptrCast(trans_lam.trans_ctx));
                    return .{ trans_ctx.local_a, trans_ctx.local_s };
                }
            }.f;

            const trans_ctx = try ctx_cfg.allocator.create(TransCtx);
            trans_ctx.local_s = s;
            trans_ctx.local_a = a;
            return .{
                .trans_lam = .{
                    .trans_fn = @constCast(&trans_fn),
                    .trans_ctx = @ptrCast(trans_ctx),
                },
                .trans_info = mkTransCtxInfo(void, .ConstantTrans),
            };
        }

        pub fn get(comptime S: type) State(S, S) {
            const trans_fn = struct {
                const RetType = Error!struct { S, S };
                fn f(trans_lam: *State(S, S).TransLam, s: S) RetType {
                    _ = trans_lam;
                    std.debug.print("get input_s: {any}\n", .{s});
                    return .{ try ctx_cfg.clone_s(s), s };
                }
            }.f;

            return .{
                .trans_lam = .{ .trans_fn = @constCast(&trans_fn) },
                .trans_info = mkTransCtxInfo(void, .NormalTrans),
            };
        }

        pub fn put(comptime S: type, s: S) Error!State(S, void) {
            const TransCtx = struct {
                local_s: S,
            };

            const trans_fn = struct {
                const RetType = Error!struct { void, S };
                fn f(trans_lam: *State(S, void).TransLam, input_s: S) RetType {
                    std.debug.print("put free input_s: {any}\n", .{input_s});
                    ctx_cfg.free_s(ctx_cfg.allocator, input_s);
                    const trans_ctx: *TransCtx = @alignCast(@ptrCast(trans_lam.trans_ctx));
                    if (S == ArrayList(i32)) {
                        std.debug.print("put load local_s.items({*})\n", .{trans_ctx.local_s.items});
                    }
                    std.debug.print("put load local_s({*}): {any}\n", .{ &trans_ctx.local_s, trans_ctx.local_s });
                    return .{ {}, trans_ctx.local_s };
                }
            }.f;
            const trans_ctx = try ctx_cfg.allocator.create(TransCtx);
            trans_ctx.local_s = s;
            if (S == ArrayList(i32)) {
                std.debug.print("put store local_s.items({*})\n", .{trans_ctx.local_s.items});
            }
            std.debug.print("put store local_s({*}): {any}\n", .{ &trans_ctx.local_s, trans_ctx.local_s });
            return .{
                .trans_lam = .{
                    .trans_fn = @constCast(&trans_fn),
                    .trans_ctx = @ptrCast(trans_ctx),
                },
                .trans_info = mkTransCtxInfo(TransCtx, .PutTrans),
            };
        }
    };
}

fn CloneTFn(comptime T: type) type {
    return *const fn (a: T) Allocator.Error!T;
}

fn FreeTFn(comptime T: type) type {
    return *const fn (Allocator, a: T) void;
}

pub fn StateCtxCfg(comptime T: type) type {
    return struct {
        allocator: Allocator,
        clone_s: CloneTFn(T),
        free_s: FreeTFn(T),
        error_set: type,
    };
}

fn getCopyAsClone(comptime T: type) CloneTFn(T) {
    return struct {
        fn f(a: T) Allocator.Error!T {
            return a;
        }
    }.f;
}

fn getFreeNothing(comptime T: type) FreeTFn(T) {
    return struct {
        fn f(allocator: Allocator, a: T) void {
            _ = allocator;
            _ = a;
        }
    }.f;
}

fn getDefaultCfg(comptime T: type, allocator: Allocator) StateCtxCfg(T) {
    return .{
        .clone_s = getCopyAsClone(T),
        .free_s = getFreeNothing(T),
        .allocator = allocator,
        .error_set = Allocator.Error,
    };
}

fn getNormalClone(comptime T: type) CloneTFn(T) {
    return struct {
        fn f(a: T) Allocator.Error!T {
            return a.clone();
        }
    }.f;
}

fn getFreeOneT(comptime T: type) FreeTFn(T) {
    return struct {
        fn f(allocator: Allocator, a: T) void {
            allocator.destroy(a);
        }
    }.f;
}

fn getDeinitOneT(comptime T: type) FreeTFn(T) {
    return struct {
        fn f(allocator: Allocator, a: T) void {
            _ = allocator;
            a.deinit();
        }
    }.f;
}

fn getDeinitCfg(comptime T: type, allocator: Allocator) StateCtxCfg(T) {
    return .{
        .clone_s = getNormalClone(T),
        .free_s = getDeinitOneT(T),
        .allocator = allocator,
        .error_set = Allocator.Error,
    };
}

test "get s from (State s a)" {
    const allocator = testing.allocator;
    const DefaultCtx = StateContext(comptime getDefaultCfg(i32, allocator));
    // const StateF = DefaultState.StateCurrying(i32);
    const state = DefaultCtx.get(i32);
    defer @constCast(&state).deinit();
    var res_a, var res_s = try @constCast(&state).runState(42);
    try testing.expectEqual(42, res_a);
    try testing.expectEqual(42, res_s);
    res_a = try @constCast(&state).evalState(17);
    res_s = try @constCast(&state).execState(-13);
    try testing.expectEqual(17, res_a);
    try testing.expectEqual(-13, res_s);
}

test "put s to (State s a)" {
    const allocator = testing.allocator;
    const DefaultCtx = StateContext(comptime getDefaultCfg(i32, allocator));
    // const StateF = DefaultState.StateCurrying(i32);
    const state = try DefaultCtx.put(i32, 42);
    defer @constCast(&state).deinit();
    var res_a, var res_s = try @constCast(&state).runState(314);
    try testing.expectEqual({}, res_a);
    try testing.expectEqual(42, res_s);
    res_a = try @constCast(&state).evalState(17);
    res_s = try @constCast(&state).execState(-13);
    try testing.expectEqual({}, res_a);
    try testing.expectEqual(42, res_s);
}

pub fn StateMonadImpl(comptime cfg: anytype, comptime S: type) type {
    return struct {
        allocator: Allocator,

        const Self = @This();

        /// State context of all states in this Monad instance
        pub const Ctx = StateContext(cfg);
        const ctx_cfg = Ctx.ctx_cfg;
        const State = Ctx.State;

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = Ctx.StateCurrying(S);

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime StateType: type) type {
            return StateType.StateA;
        }

        pub const Error = Allocator.Error || cfg.error_set;

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
            fa: anytype, // Maybe(A)
            comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
        ) void {
            _ = free_fn;
            @constCast(&fa).deinit();
        }

        fn TransFnRetType(
            comptime RetS: type,
            comptime RetA: type,
        ) type {
            const has_err, const _A = comptime isErrorUnionOrVal(RetA);
            const info = @typeInfo(RetA);
            const RetE = Error || if (has_err) info.ErrorUnion.error_set else error{};
            return RetE!struct { _A, RetS };
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            _ = self;
            const A = MapFnInType(@TypeOf(map_fn));
            const B = MapFnRetType(@TypeOf(map_fn));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            const TransCtx = struct {
                // a postfix map function, type is fn (A) B
                map_fn: *const fn (A) B,
                // a local temporary state value for fa
                local_state: State(S, A),
            };

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const trans_ctx: *TransCtx = @alignCast(@ptrCast(trans_lam.trans_ctx));
                    std.debug.print("fmap input_s: {any}\n", .{input_s});
                    const a, const s = try trans_ctx.local_state.runState(input_s);
                    const b = trans_ctx.map_fn(a);
                    std.debug.print("fmap output_s: {any}\n", .{s});
                    if (has_err) {
                        return .{ try b, s };
                    } else {
                        return .{ b, s };
                    }
                }
            }.f;

            const trans_ctx = try ctx_cfg.allocator.create(TransCtx);
            trans_ctx.map_fn = map_fn;
            trans_ctx.local_state = fa;
            return .{
                .trans_lam = .{
                    .trans_fn = @constCast(&trans_fn),
                    .trans_ctx = @ptrCast(trans_ctx),
                },
                .trans_info = mkTransCtxInfo(TransCtx, .FmapTrans),
            };
        }

        pub fn fmapLam(
            self: *Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            _ = self;
            const A = MapLamInType(@TypeOf(map_lam));
            const B = MapLamRetType(@TypeOf(map_lam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            const TransCtx = struct {
                // a postfix map function, type is fn (A) B
                map_lam: @TypeOf(map_lam),
                // a local temporary state value for fa
                local_state: State(S, A),
            };

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const trans_ctx: *TransCtx = @alignCast(@ptrCast(trans_lam.trans_ctx));
                    std.debug.print("fmapLam input_s: {any}\n", .{input_s});
                    const a, const s = try trans_ctx.local_state.runState(input_s);
                    const b = trans_ctx.map_lam.call(a);
                    std.debug.print("fmapLam output_s: {any}\n", .{s});
                    if (has_err) {
                        return .{ try b, s };
                    } else {
                        return .{ b, s };
                    }
                }
            }.f;

            const trans_ctx = try ctx_cfg.allocator.create(TransCtx);
            trans_ctx.map_lam = map_lam;
            trans_ctx.local_state = fa;
            return .{
                .trans_lam = .{
                    .trans_fn = @constCast(&trans_fn),
                    .trans_ctx = @ptrCast(trans_ctx),
                },
                .trans_info = mkTransCtxInfo(TransCtx, .FmapTrans),
            };
        }

        pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
            _ = self;
            const A = @TypeOf(a);
            const has_err, const _A = comptime isErrorUnionOrVal(A);
            const _a: _A = if (has_err) try a else a;

            const TransCtx = struct {
                // a temporary value for pure function
                local_a: _A,
            };

            const trans_fn = struct {
                const RetType = TransFnRetType(S, A);
                fn f(trans_lam: *State(S, _A).TransLam, input_s: S) RetType {
                    const trans_ctx: *TransCtx = @alignCast(@ptrCast(trans_lam.trans_ctx));
                    return .{ trans_ctx.local_a, input_s };
                }
            }.f;

            const trans_ctx = try ctx_cfg.allocator.create(TransCtx);
            trans_ctx.local_a = _a;
            return .{
                .trans_lam = .{
                    .trans_fn = @constCast(&trans_fn),
                    .trans_ctx = @ptrCast(trans_ctx),
                },
                .trans_info = mkTransCtxInfo(TransCtx, .PureTrans),
            };
        }

        pub fn fapply(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            ff: F(*const fn (A) B),
            fa: F(A),
        ) AFbType(B) {
            _ = self;
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            const TransCtx = struct {
                // a local temporary state function with type: fn (A) B
                local_state_f: State(S, *const fn (A) B),
                // a local temporary state value for fa
                local_state: State(S, A),
            };

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const trans_ctx: *TransCtx = @alignCast(@ptrCast(trans_lam.trans_ctx));
                    const af, const s1 = try trans_ctx.local_state_f.runState(input_s);
                    const a, const s2 = try trans_ctx.local_state.runState(s1);
                    const b = af(a);
                    if (has_err) {
                        return .{ try b, s2 };
                    } else {
                        return .{ b, s2 };
                    }
                }
            }.f;

            const trans_ctx = try ctx_cfg.allocator.create(TransCtx);
            trans_ctx.local_state_f = ff;
            trans_ctx.local_state = fa;
            return .{
                .trans_lam = .{
                    .trans_fn = @constCast(&trans_fn),
                    .trans_ctx = @ptrCast(trans_ctx),
                },
                .trans_info = mkTransCtxInfo(TransCtx, .FapplyTrans),
            };
        }

        pub fn fapplyLam(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(A),
        ) AFbType(B) {
            _ = self;
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            const TransCtx = struct {
                // a local temporary state function with type: fn (A) B
                local_state_lam: @TypeOf(flam),
                // a local temporary state value for fa
                local_state: State(S, A),
            };

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const trans_ctx: *TransCtx = @alignCast(@ptrCast(trans_lam.trans_ctx));
                    const alam, const s1 = try trans_ctx.local_state_lam.runState(input_s);
                    const a, const s2 = try trans_ctx.local_state.runState(s1);
                    const b = @constCast(&alam).call(a);
                    if (has_err) {
                        return .{ try b, s2 };
                    } else {
                        return .{ b, s2 };
                    }
                }
            }.f;

            const trans_ctx = try ctx_cfg.allocator.create(TransCtx);
            trans_ctx.local_state_lam = flam;
            trans_ctx.local_state = fa;
            return .{
                .trans_lam = .{
                    .trans_fn = @constCast(&trans_fn),
                    .trans_ctx = @ptrCast(trans_ctx),
                },
                .trans_info = mkTransCtxInfo(TransCtx, .FapplyTrans),
            };
        }

        pub fn bind(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*Self, A) MbType(B),
        ) MbType(B) {
            const TransCtx = struct {
                // a pointer of state monad instance
                monad_impl: *Self,
                // a local temporary state value for ma
                local_state: State(S, A),
                // a local temporary continuation function of bind function
                local_k: @TypeOf(k),
            };

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, B).TransLam, input_s: S) RetType {
                    const trans_ctx: *TransCtx = @alignCast(@ptrCast(trans_lam.trans_ctx));
                    std.debug.print("bind input_s: {any}\n", .{input_s});
                    const a, const s = try trans_ctx.local_state.runState(input_s);
                    std.debug.print("bind run ma output_s: {any}\n", .{s});
                    const state = try trans_ctx.local_k(trans_ctx.monad_impl, a);
                    defer @constCast(&state).deinit();
                    var out_a, var out_s = try @constCast(&state).runState(s);
                    _ = &out_a;
                    _ = &out_s;
                    std.debug.print("bind run (k a) output_s: {any}\n", .{out_s});
                    return .{ out_a, out_s };
                }
            }.f;

            const trans_ctx = try ctx_cfg.allocator.create(TransCtx);
            trans_ctx.monad_impl = self;
            trans_ctx.local_state = ma;
            trans_ctx.local_k = k;
            return .{
                .trans_lam = .{
                    .trans_fn = @constCast(&trans_fn),
                    .trans_ctx = @ptrCast(trans_ctx),
                },
                .trans_info = mkTransCtxInfo(TransCtx, .BindTrans),
            };
        }
    };
}

// These functions are used for unit test
const add10 = testu.add10;
const add_pi_f32 = testu.add_pi_f32;
const add_pi_f64 = testu.add_pi_f64;
const mul_pi_f64 = testu.mul_pi_f64;
const add_e_f64 = testu.add_e_f64;
const mul_e_f64 = testu.mul_e_f64;

const Add_x_f64_Lam = testu.Add_x_f64_Lam;

test "State(s, a) Functor fmap" {
    const allocator = testing.allocator;
    const default_cfg = comptime getDefaultCfg(u32, allocator);
    const DefaultCtx = StateContext(default_cfg);
    const StateFunctor = Functor(StateMonadImpl(default_cfg, u32));
    var state_functor = StateFunctor.init(.{ .allocator = allocator });

    // test fmap
    // const StateF = DefaultState.StateCurrying(u32);
    const state_a = DefaultCtx.get(u32);
    defer @constCast(&state_a).deinit();
    var state_b = try state_functor.fmap(.NewValMap, add_pi_f64, state_a);
    defer @constCast(&state_b).deinit();
    var res_a, var res_s = try @constCast(&state_b).runState(42);
    try testing.expectEqual(45.14, res_a);
    try testing.expectEqual(42, res_s);
    res_a = try @constCast(&state_b).evalState(17);
    res_s = try @constCast(&state_b).execState(17);
    try testing.expectEqual(20.14, res_a);
    try testing.expectEqual(17, res_s);

    // test fmapLam
    const add_x_f64_lam = Add_x_f64_Lam{ ._x = 3.14 };
    const state_u32 = try state_functor.fmap(.NewValMap, add10, state_a);
    defer @constCast(&state_u32).deinit();
    state_b.deinit();
    state_b = try state_functor.fmapLam(.NewValMap, add_x_f64_lam, state_u32);
    defer @constCast(&state_b).deinit();
    res_a, res_s = try @constCast(&state_b).runState(42);
    try testing.expectEqual(55.14, res_a);
    try testing.expectEqual(42, res_s);

    // test State(ArrayList(u32), a) fmap
    const ArrayListU32 = ArrayList(u32);
    const array_cfg = comptime getDeinitCfg(ArrayListU32, allocator);
    const ArrayStCtx = StateContext(array_cfg);
    const ArrayStFunctor = Functor(StateMonadImpl(array_cfg, ArrayListU32));
    var array_st_functor = ArrayStFunctor.init(.{ .allocator = allocator });

    const array_st_a = ArrayStCtx.get(ArrayListU32);
    defer @constCast(&array_st_a).deinit();
    const array_st_b = try array_st_functor.fmapLam(.NewValMap, struct {
        allocator: Allocator,
        const Self = @This();
        pub fn call(self: *Self, a: ArrayListU32) Allocator.Error!ArrayListU32 {
            var array_b = ArrayListU32.init(self.allocator);
            for (a.items, 0..) |item, i| {
                try @constCast(&array_b).append(item + @as(u32, @intCast(i)));
            }
            a.deinit();
            return array_b;
        }
    }{ .allocator = allocator }, array_st_a);
    defer @constCast(&array_st_b).deinit();

    var array_s = ArrayListU32.init(allocator);
    try array_s.appendSlice(&[_]u32{ 2, 5, 7, 8 });
    const res1_a, const res1_s = try @constCast(&array_st_b).runState(array_s);
    defer res1_a.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{ 2, 6, 9, 11 }, res1_a.items);
    try testing.expectEqualSlices(u32, &[_]u32{ 2, 5, 7, 8 }, res1_s.items);

    const array_st_c = try array_st_functor.fmap(.NewValMap, struct {
        pub fn f(a: ArrayListU32) f64 {
            defer a.deinit();
            var res_u32: u32 = 0;
            for (a.items) |item| {
                res_u32 += item;
            }
            return @as(f64, @floatFromInt(res_u32)) + 3.14;
        }
    }.f, array_st_b);
    defer @constCast(&array_st_c).deinit();
    const res2_a, const res2_s = try @constCast(&array_st_c).runState(array_s);
    defer res2_s.deinit();
    try testing.expectEqual(31.14, res2_a);
    try testing.expectEqualSlices(u32, &[_]u32{ 2, 5, 7, 8 }, res2_s.items);
}

test "State(s, a) Applicative pure and fapply" {
    // test State(u32, a)
    const allocator = testing.allocator;
    const default_cfg = comptime getDefaultCfg(u32, allocator);
    const DefaultCtx = StateContext(default_cfg);
    _ = DefaultCtx;
    const StateApplicative = Applicative(StateMonadImpl(default_cfg, u32));
    var state_applicative = StateApplicative.init(.{ .allocator = allocator });

    const state_a = try state_applicative.pure(@as(u32, 13));
    defer @constCast(&state_a).deinit();
    const pured_a, const pured_s = try @constCast(&state_a).runState(42);
    try testing.expectEqual(13, pured_a);
    try testing.expectEqual(42, pured_s);

    // the comptime function must be a const function pointer
    const add_pi_f64_p: *const @TypeOf(add_pi_f64) = add_pi_f64;
    const state_f = try state_applicative.pure(add_pi_f64_p);
    defer @constCast(&state_f).deinit();
    var state_b = try state_applicative.fapply(u32, f64, state_f, state_a);
    var res1_a, var res1_s = try @constCast(&state_b).runState(42);
    try testing.expectEqual(16.14, res1_a);
    try testing.expectEqual(42, res1_s);

    const add_x_f64_lam = Add_x_f64_Lam{ ._x = 3.14 };
    const state_lam = try state_applicative.pure(add_x_f64_lam);
    defer @constCast(&state_lam).deinit();
    state_b.deinit();
    state_b = try state_applicative.fapplyLam(u32, f64, state_lam, state_a);
    defer @constCast(&state_b).deinit();
    res1_a, res1_s = try @constCast(&state_b).runState(42);
    try testing.expectEqual(16.14, res1_a);
    try testing.expectEqual(42, res1_s);
}

test "State(s, a) Monad bind" {
    // test State(u32, a)
    const allocator = testing.allocator;
    const default_cfg = comptime getDefaultCfg(u32, allocator);
    const DefaultCtx = StateContext(default_cfg);
    const StateMonad = Monad(StateMonadImpl(default_cfg, u32));
    var state_monad = StateMonad.init(.{ .allocator = allocator });

    const state_a = try state_monad.pure(@as(u32, 13));
    defer @constCast(&state_a).deinit();
    const pured_a, const pured_s = try @constCast(&state_a).runState(42);
    try testing.expectEqual(13, pured_a);
    try testing.expectEqual(42, pured_s);

    const state_binded = try state_monad.bind(u32, f64, state_a, struct {
        fn f(inst: *@TypeOf(state_monad), a: u32) StateMonad.MbType(f64) {
            const state_b = DefaultCtx.get(u32);
            defer @constCast(&state_b).deinit();
            const add_x_f64_lam = Add_x_f64_Lam{ ._x = @floatFromInt(a) };
            return inst.fmapLam(.NewValMap, add_x_f64_lam, state_b);
        }
    }.f);
    defer @constCast(&state_binded).deinit();
    const res1_a, const res1_s = try @constCast(&state_binded).runState(42);
    try testing.expectEqual(55.0, res1_a);
    try testing.expectEqual(42, res1_s);
}

test "runDo Arraylist" {
    const input1: i32 = 42;

    const allocator = testing.allocator;
    const ArrayListMonad = Monad(ArrayListMonadImpl);
    const arraylist_m = ArrayListMonad.init(.{ .allocator = allocator });

    const array_cfg = comptime getDeinitCfg(ArrayList(i32), allocator);
    const ArrayStCtx = StateContext(array_cfg);
    const ArrayStImpl = StateMonadImpl(array_cfg, ArrayList(i32));
    const StateMonad = Monad(ArrayStImpl);
    const state_monad = StateMonad.init(.{ .allocator = allocator });

    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: ArrayStImpl,
        arrayl_monad: ArrayListMonadImpl,
        param1: i32,

        // intermediate variable
        as: ArrayList(i32) = undefined,
        b: u32 = undefined,

        const Ctx = @This();
        pub const is_pure = false;

        fn deinit(ctx: Ctx) void {
            ctx.as.deinit();
        }

        // the do context struct must has startDo function
        pub fn startDo(impl: *ArrayStImpl) ArrayStImpl.MbType(ArrayList(i32)) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            _ = ctx;
            return ArrayStCtx.get(ArrayList(i32));
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *ArrayStImpl, as: ArrayList(i32)) ArrayStImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.as = as;
            var array_s = try ctx.arrayl_monad.fmap(.NewValMap, struct {
                fn f(in: i32) i32 {
                    return in + 2;
                }
            }.f, as);
            _ = &array_s;
            std.debug.print("do1 array_s: {any}\n", .{array_s});
            const state_a = try ArrayStCtx.put(ArrayList(i32), array_s);
            // defer @constCast(&state_a).deinit();
            var state_c = impl.fmap(.NewValMap, struct {
                fn f(in: void) u32 {
                    _ = in;
                    return 37;
                }
            }.f, state_a);
            std.debug.print("do1 state_c: {any}\n", .{state_c});
            _ = &state_c;
            return state_c;
        }

        // the name of other do step function must be starts with "do" string
        // pub fn do2(impl: *ArrayStImpl, b: u32) ArrayStImpl.MbType(void) {
        //     const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
        //     ctx.b = b;

        //     // const array = try ctx.arrayl_monad.fmapLam(.InplaceMap, struct {
        //     //     local_b: u32,
        //     //     const Self = @This();
        //     //     pub fn call(self: *const Self, in: i32) i32 {
        //     //         return in + @as(i32, @intCast(self.local_b));
        //     //     }
        //     // }{ .local_b = b }, ctx.as);
        //     std.debug.print("runDo do2 ctx.as: {any}\n", .{ctx.as});
        //     return ArrayStCtx.put(ArrayList(i32), ctx.as);
        //     // const state_a = try ArrayStCtx.put(ArrayList(i32), array);
        //     // defer @constCast(&state_a).deinit();
        //     // return impl.fmap(.NewValMap, struct {
        //     //     fn f(in: void) f64 {
        //     //         _ = in;
        //     //         return 2.71828;
        //     //     }
        //     // }.f, state_a);
        // }
    }{ .monad_impl = state_monad, .arrayl_monad = arraylist_m, .param1 = input1 };
    defer do_ctx.deinit();
    const out = try runDo(&do_ctx);
    defer @constCast(&out).deinit();

    const as = &([_]i32{ 17, 42 } ** 2);
    var array = ArrayList(i32).init(allocator);
    try array.appendSlice(as);
    const res_a, const res_s = try @constCast(&out).runState(array);
    defer res_s.deinit();
    // try testing.expectEqual(2.71828, res_a);
    try testing.expectEqual(37, res_a);
    // try testing.expectEqual({}, res_a);
    std.debug.print("test runDo res_s: {any}\n", .{res_s});
    try testing.expectEqualSlices(
        i32,
        &[_]i32{ 19, 44, 19, 44 },
        res_s.items,
    );
}

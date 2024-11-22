//! Definition of State struct, these is a instance of Functor|Applicative|Monad
//! typeclass.

const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const freetypes = @import("free_types.zig");
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
const NatTrans = functor.NatTrans;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;
const ArrayListMonadImpl = arraym.ArrayListMonadImpl;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

pub fn StateContext(comptime cfg: anytype) type {
    return struct {
        pub const ctx_cfg = cfg;
        const Error = ctx_cfg.error_set;

        // the currying form of State function
        pub fn StateCurrying(comptime S: type) TCtor {
            return struct {
                fn StateTCtor(comptime A: type) type {
                    return struct {
                        ref_count: u32,
                        // translate action lambda for State
                        trans_lam: TransLam,

                        const Self = @This();
                        pub const StateS = S;
                        pub const StateA = A;
                        pub const StateAS = struct { A, S };
                        pub const TransLam = struct {
                            // the parent struct that include state and trans_ctx
                            state_parent: *anyopaque,
                            free_parent: *const fn (self: *TransLam) void,
                            trans_fn: *const fn (self: *TransLam, s: S) RetType,

                            const RetType = Error!StateAS;
                            // translate action function for State
                            pub inline fn call(trans_lam: *TransLam, s: S) RetType {
                                return trans_lam.trans_fn(trans_lam, s);
                            }
                        };
                        pub const free_s = ctx_cfg.free_s;

                        pub fn strongRef(state_self: *Self) *Self {
                            state_self.ref_count += 1;
                            return state_self;
                        }

                        pub fn strongUnref(state_self: *Self) bool {
                            if (state_self.ref_count > 1) {
                                state_self.ref_count -= 1;
                                return false;
                            }
                            state_self.ref_count = 0;
                            // free the parent struct of state struct
                            state_self.trans_lam.free_parent(&state_self.trans_lam);
                            return true;
                        }

                        /// This function run the function trans_fn in State(S, A) state,
                        /// and return result of trans_fn.
                        /// The parameter s is initial value of S for runState, this
                        /// functin should consume parameter s.
                        pub inline fn runState(state_self: *Self, s: S) Error!StateAS {
                            const trans_lam = state_self.trans_lam;
                            return @constCast(&trans_lam).call(s);
                        }
                    };
                }
            }.StateTCtor;
        }

        /// The State(S, A) is just a wrapper of lambda function with type S -> (A, S).
        pub fn State(comptime S: type, comptime A: type) type {
            return StateCurrying(S)(A);
        }

        fn StateTypeFromLam(LamType: anytype) type {
            const S = MapLamInType(LamType);
            const RetType = MapLamRetType(LamType);
            const has_err, const TupleAS = isErrorUnionOrVal(RetType);
            _ = has_err;
            const tuple_info = @typeInfo(TupleAS);

            if (!(tuple_info == .Struct and
                tuple_info.Struct.is_tuple and
                tuple_info.Struct.fields.len == 2))
            {
                @compileError("Expect return type of lam is a 2-tuple, found '" ++
                    @typeName(TupleAS) ++ "'");
            }

            const A = tuple_info.Struct.fields[0].type;
            comptime assert(S == tuple_info.Struct.fields[1].type);
            return State(S, A);
        }

        /// Create a State from a lambda, this function will consume the parameter lam.
        pub fn mkStateFromLam(lam: anytype) Error!*StateTypeFromLam(@TypeOf(lam)) {
            const LamType = @TypeOf(lam);
            const StateType = StateTypeFromLam(LamType);
            const S = StateType.StateS;
            const A = StateType.StateA;
            const TransCtx = struct {
                action_lam: LamType,
            };

            const FromLamStateType = struct {
                state: State(S, A),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, A).TransLam) void {
                    const state_parent: *FromLamStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    base.deinitOrUnref(state_parent.trans_ctx.action_lam);
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = Error!State(S, A).StateAS;
                fn f(trans_lam: *State(S, A).TransLam, input_s: S) RetType {
                    ctx_cfg.free_s(ctx_cfg.allocator, input_s);
                    const state_parent: *FromLamStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: TransCtx = state_parent.trans_ctx;
                    return trans_ctx.action_lam.call(input_s);
                }
            }.f;

            var const_state = try ctx_cfg.allocator.create(FromLamStateType);
            const_state.state.ref_count = 1;
            const_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            const_state.state.trans_lam.free_parent = free_parent;
            const_state.state.trans_lam.state_parent = @ptrCast(const_state);
            const_state.trans_ctx.action_lam = lam;
            return &const_state.state;
        }

        pub fn mkConstantState(comptime S: type, comptime A: type, s: S, a: A) Error!*State(S, A) {
            const TransCtx = struct {
                local_s: ?S,
                local_a: A,
            };

            const ConstStateType = struct {
                state: State(S, A),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, A).TransLam) void {
                    const state_parent: *ConstStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    if (state_parent.trans_ctx.local_s) |local_s| {
                        ctx_cfg.free_s(ctx_cfg.allocator, local_s);
                    }
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = Error!State(S, A).StateAS;
                fn f(trans_lam: *State(S, A).TransLam, input_s: S) RetType {
                    ctx_cfg.free_s(ctx_cfg.allocator, input_s);
                    const state_parent: *ConstStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    defer trans_ctx.local_s = null;
                    return .{ trans_ctx.local_a, trans_ctx.local_s.? };
                }
            }.f;

            var const_state = try ctx_cfg.allocator.create(ConstStateType);
            const_state.state.ref_count = 1;
            const_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            const_state.state.trans_lam.free_parent = free_parent;
            const_state.state.trans_lam.state_parent = @ptrCast(const_state);
            const_state.trans_ctx.local_s = s;
            const_state.trans_ctx.local_a = a;
            return &const_state.state;
        }

        pub fn get(comptime S: type) Error!*State(S, S) {
            const GetStateType = struct {
                state: State(S, S),
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, S).TransLam) void {
                    const state_parent: *GetStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = Error!struct { S, S };
                fn f(trans_lam: *State(S, S).TransLam, s: S) RetType {
                    _ = trans_lam;
                    return .{ try ctx_cfg.clone_s(s), s };
                }
            }.f;

            var get_state = try ctx_cfg.allocator.create(GetStateType);
            get_state.state.ref_count = 1;
            get_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            get_state.state.trans_lam.free_parent = @constCast(&free_parent);
            get_state.state.trans_lam.state_parent = @ptrCast(get_state);
            return &get_state.state;
        }

        pub fn put(comptime S: type, s: S) Error!*State(S, void) {
            const TransCtx = struct {
                local_s: ?S,
            };

            const PutStateType = struct {
                state: State(S, void),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, void).TransLam) void {
                    const state_parent: *PutStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    if (state_parent.trans_ctx.local_s) |local_s| {
                        ctx_cfg.free_s(ctx_cfg.allocator, local_s);
                    }
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = Error!struct { void, S };
                fn f(trans_lam: *State(S, void).TransLam, input_s: S) RetType {
                    ctx_cfg.free_s(ctx_cfg.allocator, input_s);
                    const state_parent: *PutStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    defer trans_ctx.local_s = null;
                    return .{ {}, trans_ctx.local_s.? };
                }
            }.f;
            var put_state = try ctx_cfg.allocator.create(PutStateType);
            put_state.state.ref_count = 1;
            put_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            put_state.state.trans_lam.free_parent = @constCast(&free_parent);
            put_state.state.trans_lam.state_parent = @ptrCast(put_state);
            put_state.trans_ctx.local_s = s;
            return &put_state.state;
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
    var state = try DefaultCtx.get(i32);
    defer _ = state.strongUnref();
    const res_a, const res_s = try state.runState(42);
    try testing.expectEqual(42, res_a);
    try testing.expectEqual(42, res_s);
}

test "put s to (State s a)" {
    const allocator = testing.allocator;
    const DefaultCtx = StateContext(comptime getDefaultCfg(i32, allocator));
    const state = try DefaultCtx.put(i32, 42);
    defer _ = state.strongUnref();
    const res_a, const res_s = try state.runState(314);
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
        pub fn F(comptime A: type) type {
            return *Ctx.State(S, A);
        }

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime PState: type) type {
            return std.meta.Child(PState).StateA;
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
            _ = fa.strongUnref();
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
                local_state: *State(S, A),
            };

            const FmapStateType = struct {
                state: State(S, _B),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, _B).TransLam) void {
                    const state_parent: *FmapStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const state_parent: *FmapStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const a, const s = try trans_ctx.local_state.runState(input_s);
                    _ = trans_ctx.local_state.strongUnref();
                    const b = trans_ctx.map_fn(a);
                    if (has_err) {
                        return .{ try b, s };
                    } else {
                        return .{ b, s };
                    }
                }
            }.f;

            var fmap_state = try ctx_cfg.allocator.create(FmapStateType);
            fmap_state.state.ref_count = 1;
            fmap_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            fmap_state.state.trans_lam.free_parent = @constCast(&free_parent);
            fmap_state.state.trans_lam.state_parent = @ptrCast(fmap_state);
            fmap_state.trans_ctx.map_fn = map_fn;
            fmap_state.trans_ctx.local_state = fa.strongRef();
            return &fmap_state.state;
        }

        pub fn fmapLam(
            self: *const Self,
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
                local_state: *State(S, A),
            };

            const FmapLamStateType = struct {
                state: State(S, _B),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, _B).TransLam) void {
                    const state_parent: *FmapLamStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const state_parent: *FmapLamStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const a, const s = try trans_ctx.local_state.runState(input_s);
                    _ = trans_ctx.local_state.strongUnref();
                    const b = trans_ctx.map_lam.call(a);
                    if (has_err) {
                        return .{ try b, s };
                    } else {
                        return .{ b, s };
                    }
                }
            }.f;

            var fmaplam_state = try ctx_cfg.allocator.create(FmapLamStateType);
            fmaplam_state.state.ref_count = 1;
            fmaplam_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            fmaplam_state.state.trans_lam.free_parent = @constCast(&free_parent);
            fmaplam_state.state.trans_lam.state_parent = @ptrCast(fmaplam_state);
            fmaplam_state.trans_ctx.map_lam = map_lam;
            fmaplam_state.trans_ctx.local_state = fa.strongRef();
            return &fmaplam_state.state;
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

            const PureStateType = struct {
                state: State(S, _A),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, _A).TransLam) void {
                    const state_parent: *PureStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, A);
                fn f(trans_lam: *State(S, _A).TransLam, input_s: S) RetType {
                    const state_parent: *PureStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    return .{ trans_ctx.local_a, input_s };
                }
            }.f;

            var pure_state = try ctx_cfg.allocator.create(PureStateType);
            pure_state.state.ref_count = 1;
            pure_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            pure_state.state.trans_lam.free_parent = @constCast(&free_parent);
            pure_state.state.trans_lam.state_parent = @ptrCast(pure_state);
            pure_state.trans_ctx.local_a = _a;
            return &pure_state.state;
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
                local_state_f: *State(S, *const fn (A) B),
                // a local temporary state value for fa
                local_state: *State(S, A),
            };

            const FapplyStateType = struct {
                state: State(S, _B),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, _B).TransLam) void {
                    const state_parent: *FapplyStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const state_parent: *FapplyStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const af, const s1 = try trans_ctx.local_state_f.runState(input_s);
                    _ = trans_ctx.local_state_f.strongUnref();
                    const a, const s2 = try trans_ctx.local_state.runState(s1);
                    _ = trans_ctx.local_state.strongUnref();
                    const b = af(a);
                    if (has_err) {
                        return .{ try b, s2 };
                    } else {
                        return .{ b, s2 };
                    }
                }
            }.f;

            var fapply_state = try ctx_cfg.allocator.create(FapplyStateType);
            fapply_state.state.ref_count = 1;
            fapply_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            fapply_state.state.trans_lam.free_parent = @constCast(&free_parent);
            fapply_state.state.trans_lam.state_parent = @ptrCast(fapply_state);
            fapply_state.trans_ctx.local_state_f = ff.strongRef();
            fapply_state.trans_ctx.local_state = fa.strongRef();
            return &fapply_state.state;
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
                local_state_flam: @TypeOf(flam),
                // a local temporary state value for fa
                local_state: *State(S, A),
            };

            const FapplyLamStateType = struct {
                state: State(S, _B),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, _B).TransLam) void {
                    const state_parent: *FapplyLamStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const state_parent: *FapplyLamStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const alam, const s1 = try trans_ctx.local_state_flam.runState(input_s);
                    _ = trans_ctx.local_state_flam.strongUnref();
                    const a, const s2 = try trans_ctx.local_state.runState(s1);
                    _ = trans_ctx.local_state.strongUnref();
                    const b = @constCast(&alam).call(a);
                    if (has_err) {
                        return .{ try b, s2 };
                    } else {
                        return .{ b, s2 };
                    }
                }
            }.f;

            var fapplylam_state = try ctx_cfg.allocator.create(FapplyLamStateType);
            fapplylam_state.state.ref_count = 1;
            fapplylam_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            fapplylam_state.state.trans_lam.free_parent = @constCast(&free_parent);
            fapplylam_state.state.trans_lam.state_parent = @ptrCast(fapplylam_state);
            fapplylam_state.trans_ctx.local_state_flam = flam.strongRef();
            fapplylam_state.trans_ctx.local_state = fa.strongRef();
            return &fapplylam_state.state;
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
                local_state: *State(S, A),
                // a local temporary continuation function of bind function
                local_k: @TypeOf(k),
            };

            const BindStateType = struct {
                state: State(S, B),
                trans_ctx: TransCtx,
            };

            const free_parent = struct {
                fn freeParent(trans_lam: *State(S, B).TransLam) void {
                    const state_parent: *BindStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    ctx_cfg.allocator.destroy(state_parent);
                }
            }.freeParent;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, B).TransLam, input_s: S) RetType {
                    const state_parent: *BindStateType = @alignCast(@ptrCast(trans_lam.state_parent));
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const a, const s = try trans_ctx.local_state.runState(input_s);
                    _ = trans_ctx.local_state.strongUnref();
                    const state = try trans_ctx.local_k(trans_ctx.monad_impl, a);
                    const out_a, const out_s = try state.runState(s);
                    _ = state.strongUnref();
                    return .{ out_a, out_s };
                }
            }.f;

            var bind_state = try ctx_cfg.allocator.create(BindStateType);
            bind_state.state.ref_count = 1;
            bind_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            bind_state.state.trans_lam.free_parent = @constCast(&free_parent);
            bind_state.state.trans_lam.state_parent = @ptrCast(bind_state);
            bind_state.trans_ctx.monad_impl = self;
            bind_state.trans_ctx.local_state = ma.strongRef();
            bind_state.trans_ctx.local_k = k;
            return &bind_state.state;
        }

        pub fn join(
            self: *Self,
            comptime A: type,
            mma: F(F(A)),
        ) MbType(A) {
            const ident_k = struct {
                fn idFn(k_self: *Self, ma: F(A)) MbType(A) {
                    _ = k_self;
                    return ma;
                }
            }.idFn;
            return self.bind(F(A), A, mma, &ident_k);
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
    var state_a = try DefaultCtx.get(u32);
    defer _ = state_a.strongUnref();
    var state_b = try state_functor.fmap(.NewValMap, add_pi_f64, state_a);
    var res_a, var res_s = try state_b.runState(42);
    defer _ = state_b.strongUnref();
    try testing.expectEqual(45.14, res_a);
    try testing.expectEqual(42, res_s);

    // test fmapLam
    const add_x_f64_lam = Add_x_f64_Lam{ ._x = 3.14 };
    var state_u32 = try state_functor.fmap(.NewValMap, add10, state_a);
    defer _ = state_u32.strongUnref();
    var state_c = try state_functor.fmapLam(.NewValMap, add_x_f64_lam, state_u32);
    defer _ = state_c.strongUnref();
    res_a, res_s = try state_c.runState(42);
    try testing.expectEqual(55.14, res_a);
    try testing.expectEqual(42, res_s);

    // test State(ArrayList(u32), a) fmap
    const ArrayListU32 = ArrayList(u32);
    const array_cfg = comptime getDeinitCfg(ArrayListU32, allocator);
    const ArrayStCtx = StateContext(array_cfg);
    const ArrayStFunctor = Functor(StateMonadImpl(array_cfg, ArrayListU32));
    var array_st_functor = ArrayStFunctor.init(.{ .allocator = allocator });

    var array_st_a = try ArrayStCtx.get(ArrayListU32);
    defer _ = array_st_a.strongUnref();
    var array_st_b = try array_st_functor.fmapLam(.NewValMap, struct {
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
    defer _ = array_st_b.strongUnref();

    var array_s = ArrayListU32.init(allocator);
    try array_s.appendSlice(&[_]u32{ 2, 5, 7, 8 });
    const res1_a, const res1_s = try array_st_b.runState(array_s);
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
    defer _ = array_st_c.strongUnref();
    const res2_a, const res2_s = try array_st_c.runState(array_s);
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

    var state_a = try state_applicative.pure(@as(u32, 13));
    defer _ = state_a.strongUnref();
    const pured_a, const pured_s = try state_a.runState(42);
    try testing.expectEqual(13, pured_a);
    try testing.expectEqual(42, pured_s);

    // the comptime function must be a const function pointer
    const add_pi_f64_p: *const @TypeOf(add_pi_f64) = add_pi_f64;
    var state_f = try state_applicative.pure(add_pi_f64_p);
    defer _ = state_f.strongUnref();
    var state_b = try state_applicative.fapply(u32, f64, state_f, state_a);
    defer _ = state_b.strongUnref();
    var res1_a, var res1_s = try state_b.runState(42);
    try testing.expectEqual(16.14, res1_a);
    try testing.expectEqual(42, res1_s);

    const add_x_f64_lam = Add_x_f64_Lam{ ._x = 3.14 };
    var state_lam = try state_applicative.pure(add_x_f64_lam);
    defer _ = state_lam.strongUnref();
    var state_c = try state_applicative.fapplyLam(u32, f64, state_lam, state_a);
    defer _ = state_c.strongUnref();
    res1_a, res1_s = try state_c.runState(42);
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

    var state_a = try state_monad.pure(@as(u32, 13));
    defer _ = state_a.strongUnref();
    const pured_a, const pured_s = try state_a.runState(42);
    try testing.expectEqual(13, pured_a);
    try testing.expectEqual(42, pured_s);

    var state_binded = try state_monad.bind(u32, f64, state_a, struct {
        fn f(inst: *@TypeOf(state_monad), a: u32) StateMonad.MbType(f64) {
            var state_b = try DefaultCtx.get(u32);
            defer _ = state_b.strongUnref();
            const add_x_f64_lam = Add_x_f64_Lam{ ._x = @floatFromInt(a) };
            return inst.fmapLam(.NewValMap, add_x_f64_lam, state_b);
        }
    }.f);
    defer _ = state_binded.strongUnref();
    const res1_a, const res1_s = try state_binded.runState(42);
    try testing.expectEqual(55.0, res1_a);
    try testing.expectEqual(42, res1_s);
}

test "runDo State(Arraylist(i32), A)" {
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
        as: ?ArrayList(i32) = null,
        b: u32 = undefined,

        const Ctx = @This();
        pub const is_pure = false;

        fn deinit(ctx: Ctx) void {
            if (ctx.as) |as| {
                as.deinit();
            }
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
            var state_a = try ArrayStCtx.put(ArrayList(i32), array_s);
            defer _ = state_a.strongUnref();
            var state_c = impl.fmap(.NewValMap, struct {
                fn f(in: void) u32 {
                    _ = in;
                    return 37;
                }
            }.f, state_a);
            _ = &state_c;
            return state_c;
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *ArrayStImpl, b: u32) ArrayStImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.b = b;

            const array = try ctx.arrayl_monad.fmapLam(.InplaceMap, struct {
                local_b: u32,
                const Self = @This();
                pub fn call(self: *const Self, in: i32) i32 {
                    return in + @as(i32, @intCast(self.local_b));
                }
            }{ .local_b = b }, ctx.as.?);
            // The InplaceMap kind of fmap will consume the ctx.as
            ctx.as = null;
            // return ArrayStCtx.mkConstantState(ArrayList(i32), f64, array, 2.71828);
            const state_a = try ArrayStCtx.put(ArrayList(i32), array);
            defer _ = state_a.strongUnref();
            return impl.fmap(.NewValMap, struct {
                fn f(in: void) f64 {
                    _ = in;
                    return 2.71828;
                }
            }.f, state_a);
        }
    }{ .monad_impl = state_monad, .arrayl_monad = arraylist_m, .param1 = input1 };
    defer do_ctx.deinit();
    var out = try runDo(&do_ctx);
    defer _ = out.strongUnref();

    const as = &([_]i32{ 17, 42 } ** 2);
    var array = ArrayList(i32).init(allocator);
    try array.appendSlice(as);
    const res_a, const res_s = try out.runState(array);
    defer res_s.deinit();
    try testing.expectEqual(2.71828, res_a);
    try testing.expectEqualSlices(
        i32,
        &[_]i32{ 54, 79, 54, 79 },
        res_s.items,
    );
}

/// Define the StateF for construct Free (StateF S) A
pub fn StateF(comptime cfg: anytype, comptime S: type) TCtor {
    return struct {
        fn StateSA(comptime A: type) type {
            return union(enum) {
                GetF: *GetLamType,
                PutF: struct { S, A },

                const Self = @This();
                const GetLamType = base.ComposableLam(cfg, S, Error!A);
                pub const BaseType = A;
                pub const Error = cfg.error_set;
                pub const ExistentialType = S;
                pub const OpCtorDefs = StateFCtorDefs(cfg, S, A);
                pub const StateS = S;
                pub const StateA = A;

                pub fn effGetF(get_fn: *const fn (S) Error!A) Error!Self {
                    return .{ .GetF = try GetLamType.createByFn(get_fn) };
                }

                pub fn effPutF(s: S, a: A) Self {
                    return .{ .PutF = .{ s, a } };
                }

                pub fn deinit(self: Self) void {
                    if (self == .GetF) {
                        _ = self.GetF.strongUnref();
                    } else {
                        base.deinitOrUnref(self.PutF[0]);
                    }
                }
            };
        }
    }.StateSA;
}

pub fn StateFA(comptime cfg: anytype, comptime S: type, comptime A: type) type {
    return StateF(cfg, S)(A);
}

pub fn StateFFunctorImpl(comptime cfg: anytype, comptime S: type) type {
    return struct {
        allocator: Allocator,

        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub fn F(comptime A: type) type {
            return StateFA(cfg, S, A);
        }

        /// Get base type of F(A), it is must just is A.
        pub fn BaseType(comptime State: type) type {
            return std.meta.Child(State).StateA;
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
            fa: anytype, // StateF(cfg, S, A)
            comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
        ) void {
            _ = free_fn;
            fa.deinit();
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
            _ = _B;
            const _fa = if (comptime isMapRef(K)) fa.* else fa;

            const MapRefLam = struct {
                map_fn: @TypeOf(map_fn),
                const MapSelf = @This();
                pub fn call(map_self: MapSelf, a: std.meta.Child(A)) B {
                    return map_self.map_fn(&a);
                }
            };

            if (_fa == .GetF) {
                if (comptime isMapRef(K)) {
                    const map_ref_lam = MapRefLam{ .map_fn = map_fn };
                    return .{ .GetF = fa.GetF.appendLam(map_ref_lam) };
                }
                return .{ .GetF = fa.GetF.appendFn(map_fn) };
            } else {
                const b = if (comptime isMapRef(K))
                    map_fn(&fa.PutF[1])
                else
                    map_fn(fa.PutF[1]);
                const _b = if (has_err) try b else b;
                return .{ .PutF = .{ fa.PutF[0], _b } };
            }
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            _ = self;
            const A = MapLamInType(@TypeOf(map_lam));
            const B = MapLamRetType(@TypeOf(map_lam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;
            const _fa = if (comptime isMapRef(K)) fa.* else fa;

            const MapRefLam = struct {
                map_lam: @TypeOf(map_lam),
                const MapSelf = @This();
                pub fn deinit(map_self: MapSelf) void {
                    base.deinitOrUnref(map_self.map_lam);
                }

                pub fn call(map_self: MapSelf, a: std.meta.Child(A)) B {
                    return map_self.map_lam.call(&a);
                }
            };

            if (_fa == .GetF) {
                if (comptime isMapRef(K)) {
                    const map_ref_lam = MapRefLam{ .map_lam = map_lam };
                    return .{ .GetF = try fa.GetF.appendLam(map_ref_lam) };
                }
                return .{ .GetF = try fa.GetF.appendLam(map_lam) };
            } else {
                const b = if (comptime isMapRef(K))
                    map_lam.call(&fa.PutF[1])
                else
                    map_lam.call(fa.PutF[1]);
                const _b = if (has_err) try b else b;
                return .{ .PutF = .{ fa.PutF[0], _b } };
            }
        }
    };
}

/// All value constructors for Maybe Functor
fn StateFCtorDefs(comptime cfg: anytype, comptime S: type, comptime A: type) type {
    const Error = cfg.error_set;

    // Define Op constructor lambdas for StateF
    return struct {
        pub const PutF = PutFLam;
        pub const GetF = GetFLam;

        const PutFLam = extern struct {
            lam_ctx: ?*S = null,

            const Self = @This();
            pub fn build(s: S) Error!Self {
                const put_s = try cfg.allocator.create(S);
                put_s.* = try base.copyOrCloneOrRef(s);
                return .{ .lam_ctx = put_s };
            }

            pub fn deinit(self: Self) void {
                if (self.lam_ctx != null) {
                    base.deinitOrUnref(self.lam_ctx.?.*);
                    cfg.allocator.destroy(self.lam_ctx.?);
                }
            }

            pub fn clone(self: Self) Error!Self {
                if (self.lam_ctx != null) {
                    const new_put_s = try cfg.allocator.create(S);
                    new_put_s.* = try base.copyOrCloneOrRef(self.lam_ctx.?.*);
                    return .{ .lam_ctx = new_put_s };
                } else {
                    return .{ .lam_ctx = null };
                }
            }

            pub fn call(self: *Self, a: A) StateFA(cfg, S, A) {
                if (self.lam_ctx == null) {
                    @panic("Fatal Error: The Put of StateF is not initialized!");
                }

                return .{ .PutF = .{ self.lam_ctx.?.*, a } };
            }
        };

        const GetFLam = struct {
            // composable function
            lam_ctx: *const fn (S) Error!A,

            const Self = @This();
            // This Op is just a function that return type is A
            const is_fn_op = true;
            pub fn build(action: *const fn (S) Error!A) Self {
                return .{ .lam_ctx = action };
            }

            pub fn deinit(self: Self) void {
                _ = self;
            }

            pub fn call(self: *const Self) Error!StateFA(cfg, S, A) {
                return StateFA(cfg, S, A).effGetF(self.lam_ctx);
            }
        };
    };
}

pub fn StateFToStateNatImpl(comptime cfg: anytype, comptime S: type) type {
    const DefaultCtx = StateContext(cfg);
    return struct {
        const Self = @This();

        pub const F = StateF(cfg, S);
        pub const G = StateMonadImpl(cfg, S).F;
        pub const Error = Allocator.Error;

        pub fn trans(self: Self, comptime A: type, fa: F(A)) Error!G(A) {
            _ = self;
            if (fa == .PutF) {
                // fa.PutF is tuple of (S, State(S, A))
                // It is just as Haskell code:
                //     State $ \s -> (PutF.a, PutF.s)
                return DefaultCtx.mkConstantState(S, A, fa.PutF[0], fa.PutF[1]);
            } else {
                const action_lam = struct {
                    local_fa: F(A),
                    const LamSelf = @This();
                    pub fn deinit(lam_self: LamSelf) void {
                        lam_self.local_fa.deinit();
                    }

                    pub fn call(
                        lam_self: *const LamSelf,
                        s: S,
                    ) DefaultCtx.Error!DefaultCtx.State(S, A).StateAS {
                        // This lambda just as Haskell code:
                        //     \s -> (GetF.g s, s)
                        return .{ try lam_self.local_fa.GetF.call(s), s };
                    }
                }{ .local_fa = .{ .GetF = fa.GetF.strongRef() } };
                // It is just as Haskell code:
                //     State $ \s -> (GetF.g s, s)
                return DefaultCtx.mkStateFromLam(action_lam);
            }
        }
    };
}

pub fn StateFShowNatImpl(comptime cfg: anytype, comptime S: type) type {
    const StateFCtor = StateF(cfg, S);
    const ExistType = freetypes.GetExistentialType(StateFCtor);
    return struct {
        allocator: Allocator,

        const Self = @This();

        pub const F = StateF(cfg, S);
        pub const G = MWriterMaybe(ArrayList(u8));
        pub const Error = Allocator.Error;

        pub fn trans(self: Self, comptime A: type, fa: F(A)) Error!G(A) {
            if (fa == .PutF) {
                const put_fmt_str = "PutF {any}, ";
                const len = std.fmt.count(put_fmt_str, .{fa.PutF[0]});
                var array = try ArrayList(u8).initCapacity(self.allocator, len);
                const put_buf = array.addManyAsSliceAssumeCapacity(len);
                _ = std.fmt.bufPrint(put_buf, put_fmt_str, .{fa.PutF[0]}) catch |err|
                    switch (err) {
                    error.NoSpaceLeft => unreachable, // we just counted the size above
                };
                return .{ .a = fa.PutF[1], .w = array };
            } else {
                const get_fmt_str = "GetF, ";
                const len = std.fmt.count(get_fmt_str, .{});
                var array = try ArrayList(u8).initCapacity(self.allocator, len);
                const get_buf = array.addManyAsSliceAssumeCapacity(len);
                _ = std.fmt.bufPrint(get_buf, get_fmt_str, .{}) catch |err|
                    switch (err) {
                    error.NoSpaceLeft => unreachable, // we just counted the size above
                };
                const init_val = base.defaultVal(ExistType);
                return .{ .a = try fa.GetF.call(init_val), .w = array };
            }
        }
    };
}

fn statefToA(
    comptime cfg: anytype,
    comptime S: type,
    comptime A: type,
) *const fn (a: StateFA(cfg, S, A)) A {
    const StateFCtor = StateF(cfg, S);
    const ExistType = freetypes.GetExistentialType(StateFCtor);
    return struct {
        fn iterFn(statef: StateFA(cfg, S, A)) A {
            switch (statef) {
                .GetF => {
                    const init_val = base.defaultVal(ExistType);
                    return statef.GetF.call(init_val) catch base.defaultVal(A);
                },
                .PutF => {
                    return statef.PutF[1];
                },
            }
        }
    }.iterFn;
}

const ArrayListMonoidImpl = freetypes.ArrayListMonoidImpl;
const FreeMonad = freetypes.FreeMonad;
const FreeMonadImpl = freetypes.FreeMonadImpl;
const FOpEnumInt = freetypes.FOpEnumInt;

test "FreeMonad(StateF, A) foldFree and iter" {
    const allocator = testing.allocator;
    const StateS = u64;
    const cfg = getDefaultCfg(StateS, allocator);
    const StateFCtor = StateF(cfg, StateS);
    const StateFFunctor = Functor(StateFFunctorImpl(cfg, StateS));
    const statef_functor = StateFFunctor.init(.{ .allocator = allocator });

    const StateMonad = Monad(StateMonadImpl(cfg, StateS));
    const state_monad = StateMonad.init(.{ .allocator = allocator });
    const NatStateFToState = NatTrans(StateFToStateNatImpl(cfg, StateS));
    const nat_statef_state = NatStateFToState.init(.{});

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.init(.{ .allocator = allocator });

    const ExistType = freetypes.GetExistentialType(StateFCtor);
    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, StateS, u32));
    const PutF: FOpEnumInt = @intFromEnum(StateFCtorEnum.PutF);
    const buildPutF = StateFCtorDefs(cfg, StateS, u32).PutF.build;
    const GetF: FOpEnumInt = @intFromEnum(StateFCtorEnum.GetF);
    // The function operator build a FreeMonad(F, ExistType)
    const buildGetF = StateFCtorDefs(cfg, StateS, ExistType).GetF.build;
    const FOpInfo = freetypes.FOpInfo;
    const put_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
    };

    var free_state = try FreeMonad(StateFCtor, u32).freeM(allocator, 42, @constCast(put_ops));
    defer free_state.deinit();
    const state0 = try free_state.foldFree(nat_statef_state, statef_functor, state_monad);
    const res0_a, const res0_s = try state0.runState(13);
    _ = state0.strongUnref();
    try testing.expectEqual(42, res0_a);
    try testing.expectEqual(37, res0_s);
    const show_writer = try free_state.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer.deinit();
    try testing.expectEqual(42, show_writer.a);
    try testing.expectEqualSlices(u8, "PutF 23, PutF 37, ", show_writer.w.items);
    try testing.expectEqual(42, try free_state.iter(statef_functor, statefToA(cfg, ExistType, u32)));

    const get_fn = struct {
        const Error = FreeMonad(StateFCtor, ExistType).Error;
        fn get(s: u64) Error!ExistType {
            return @intCast(s + 10);
        }
    }.get;

    const x_to_free_state = struct {
        const Error = FreeMonad(StateFCtor, u32).Error;
        fn xToFreeState(x: ExistType) Error!FreeMonad(StateFCtor, u32) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37 + x)) },
            };
            const a = @as(u32, @intCast(x)) * 2;
            return FreeMonad(StateFCtor, u32).freeM(allocator, a, @constCast(x_state_ops));
        }
    }.xToFreeState;

    var free_state1 = try FreeMonad(StateFCtor, u32).freeFOp(x_to_free_state, GetF, buildGetF(get_fn));
    defer free_state1.deinit();
    const state1 = try free_state1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res1_a, const res1_s = try state1.runState(13);
    _ = state1.strongUnref();
    // (13 + 10) * 2 = 46
    try testing.expectEqual(46, res1_a);
    // (13 + 10) + 37 = 60
    try testing.expectEqual(60, res1_s);
    const show_writer1 = try free_state1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer1.deinit();
    // In StateFShowNatImpl, the GetF had been put a 0 as S value, so s = 0.
    // (0 + 10) * 2 = 20
    try testing.expectEqual(20, show_writer1.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "GetF, PutF 47, ", show_writer1.w.items);
    try testing.expectEqual(20, try free_state1.iter(statef_functor, statefToA(cfg, ExistType, u32)));

    const state1_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(89)) },
    };
    free_state1 = try free_state1.appendFOp(allocator, state1_ops[0]);
    const state2 = try free_state1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res2_a, const res2_s = try state2.runState(13);
    _ = state2.strongUnref();
    // (89 + 10) * 2 = 198
    try testing.expectEqual(198, res2_a);
    // (89 + 10) + 37 = 136
    try testing.expectEqual(136, res2_s);
    const show_writer2 = try free_state1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer2.deinit();
    // (0 + 10) * 2 = 20
    try testing.expectEqual(20, show_writer2.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 89, GetF, PutF 47, ", show_writer2.w.items);
    try testing.expectEqual(20, try free_state1.iter(statef_functor, statefToA(cfg, ExistType, u32)));
}

test "FreeMonad(StateF, A) fmap and fmapLam" {
    const allocator = testing.allocator;
    const StateS = u64;
    const cfg = getDefaultCfg(StateS, allocator);
    const StateFCtor = StateF(cfg, StateS);
    const StateFFunctor = Functor(StateFFunctorImpl(cfg, StateS));
    const statef_functor = StateFFunctor.init(.{ .allocator = allocator });
    const FreeStateFImpl = FreeMonadImpl(StateFCtor, StateFFunctorImpl(cfg, StateS));
    const FStateMonad = Monad(FreeStateFImpl);
    var freem_monad = FStateMonad.init(.{
        .allocator = allocator,
        .funf_impl = statef_functor,
    });

    const StateMonad = Monad(StateMonadImpl(cfg, StateS));
    const state_monad = StateMonad.init(.{ .allocator = allocator });
    const NatStateFToState = NatTrans(StateFToStateNatImpl(cfg, StateS));
    const nat_statef_state = NatStateFToState.init(.{});

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.init(.{ .allocator = allocator });

    const ExistType = freetypes.GetExistentialType(StateFCtor);
    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, StateS, u32));
    const PutF: FOpEnumInt = @intFromEnum(StateFCtorEnum.PutF);
    const buildPutF = StateFCtorDefs(cfg, StateS, u32).PutF.build;
    const GetF: FOpEnumInt = @intFromEnum(StateFCtorEnum.GetF);
    // The function operator build a FreeMonad(F, ExistType)
    const buildGetF = StateFCtorDefs(cfg, StateS, ExistType).GetF.build;
    const FOpInfo = freetypes.FOpInfo;
    const put_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
    };

    const get_fn = struct {
        const Error = FreeMonad(StateFCtor, ExistType).Error;
        fn get(s: u64) Error!ExistType {
            return @intCast(s + 10);
        }
    }.get;

    const x_to_free_state = struct {
        const Error = FreeMonad(StateFCtor, u32).Error;
        fn xToFreeState(x: u64) Error!FreeMonad(StateFCtor, u32) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37 + x)) },
            };
            const a = @as(u32, @intCast(x)) * 2;
            return FreeMonad(StateFCtor, u32).freeM(allocator, a, @constCast(x_state_ops));
        }
    }.xToFreeState;

    var free_state = try FreeMonad(StateFCtor, u32).freeFOp(x_to_free_state, GetF, buildGetF(get_fn));

    free_state = try free_state.appendFOps(allocator, put_ops);
    // When use InplaceMap mode to call fmap with free_state, do not deinit free_state.
    // defer free_state.deinit();
    const state0 = try free_state.foldFree(nat_statef_state, statef_functor, state_monad);
    const res0_a, const res0_s = try state0.runState(13);
    _ = state0.strongUnref();
    // (37 + 10) * 2 = 94
    try testing.expectEqual(94, res0_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res0_s);
    const show_writer = try free_state.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer.deinit();
    // (0 + 10) * 2 = 20
    try testing.expectEqual(20, show_writer.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 23, PutF 37, GetF, PutF 47, ", show_writer.w.items);

    // const add_pi_f64_lam = testu.Add_x_f64_Lam{ ._x = 3.14 };
    // const free_state1 = try freem_monad.fmapLam(.InplaceMap, add_pi_f64_lam, free_state);
    const free_state1 = try freem_monad.fmap(.InplaceMap, add_pi_f64, free_state);
    // When use InplaceMap mode to call fmap with free_state1, do not deinit free_state1.
    // defer free_state1.deinit();
    const state1 = try free_state1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res1_a, const res1_s = try state1.runState(13);
    _ = state1.strongUnref();
    // (37 + 10) * 2 + 3.14 = 97.14
    try testing.expectEqual(97.14, res1_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res1_s);
    const show_writer1 = try free_state1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer1.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer1.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 23, PutF 37, GetF, PutF 47, ", show_writer1.w.items);

    const div_5_u32_lam = testu.Div_x_u32_Lam{ ._x = 5 };
    const free_state2 = try freem_monad.fmapLam(.InplaceMap, div_5_u32_lam, free_state1);
    defer free_state2.deinit();
    const state2 = try free_state2.foldFree(nat_statef_state, statef_functor, state_monad);
    const res2_a, const res2_s = try state2.runState(13);
    _ = state2.strongUnref();
    // ((37 + 10) * 2 + 3.14) / 5 = 19
    try testing.expectEqual(19, res2_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res2_s);
    const show_writer2 = try free_state2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer2.deinit();
    // ((0 + 10) * 2 + 3.14) / 5 = 4
    try testing.expectEqual(4, show_writer2.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 23, PutF 37, GetF, PutF 47, ", show_writer2.w.items);
}

test "FreeMonad(StateF, A) fapply and fapplyLam" {
    const allocator = testing.allocator;
    const StateS = u64;
    const cfg = getDefaultCfg(StateS, allocator);
    const StateFCtor = StateF(cfg, StateS);
    const StateFFunctor = Functor(StateFFunctorImpl(cfg, StateS));
    const statef_functor = StateFFunctor.init(.{ .allocator = allocator });
    const FreeStateFImpl = FreeMonadImpl(StateFCtor, StateFFunctorImpl(cfg, StateS));
    const FStateMonad = Monad(FreeStateFImpl);
    var freem_monad = FStateMonad.init(.{
        .allocator = allocator,
        .funf_impl = statef_functor,
    });

    const StateMonad = Monad(StateMonadImpl(cfg, StateS));
    const state_monad = StateMonad.init(.{ .allocator = allocator });
    const NatStateFToState = NatTrans(StateFToStateNatImpl(cfg, StateS));
    const nat_statef_state = NatStateFToState.init(.{});

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.init(.{ .allocator = allocator });

    const ExistType = freetypes.GetExistentialType(StateFCtor);
    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, StateS, u32));
    const PutF: FOpEnumInt = @intFromEnum(StateFCtorEnum.PutF);
    const buildPutF = StateFCtorDefs(cfg, StateS, u32).PutF.build;
    const GetF: FOpEnumInt = @intFromEnum(StateFCtorEnum.GetF);
    // The function operator build a FreeMonad(F, ExistType)
    const buildGetF = StateFCtorDefs(cfg, StateS, ExistType).GetF.build;
    const FOpInfo = freetypes.FOpInfo;

    // test all variants of FreeMonad StateF A with pure value
    const put_a_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(25)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(19)) },
    };
    const put_af_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(17)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(35)) },
    };
    const put_flam_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(17)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(35)) },
    };

    const pure_free_a = try freem_monad.pure(@as(u32, 42));
    const pure_free_a1 = try pure_free_a.appendFOps(allocator, put_a_ops);
    defer pure_free_a1.deinit();
    const pure_free_af = try freem_monad.pure(&add_pi_f64);
    const pure_free_af1 = try pure_free_af.appendFOps(allocator, put_af_ops);
    defer pure_free_af1.deinit();
    const add_pi_f64_lam = testu.Add_x_f64_Lam{ ._x = 3.14 };
    const pure_free_flam = try freem_monad.pure(add_pi_f64_lam);
    const pure_free_flam1 = try pure_free_flam.appendFOps(allocator, put_flam_ops);
    defer pure_free_flam1.deinit();

    const pure_applied1 = try freem_monad.fapply(u32, f64, pure_free_af1, pure_free_a);
    defer pure_applied1.deinit();
    const pure_state1 = try pure_applied1.foldFree(nat_statef_state, statef_functor, state_monad);
    const pure_res1_a, const pure_res1_s = try pure_state1.runState(13);
    _ = pure_state1.strongUnref();
    try testing.expectEqual(45.14, pure_res1_a);
    try testing.expectEqual(17, pure_res1_s);
    const show_pure1 = try pure_applied1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_pure1.deinit();
    try testing.expectEqual(45.14, show_pure1.a);
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, ", show_pure1.w.items);

    const pure_applied2 = try freem_monad.fapply(u32, f64, pure_free_af1, pure_free_a1);
    defer pure_applied2.deinit();
    const pure_state2 = try pure_applied2.foldFree(nat_statef_state, statef_functor, state_monad);
    const pure_res2_a, const pure_res2_s = try pure_state2.runState(13);
    _ = pure_state2.strongUnref();
    try testing.expectEqual(45.14, pure_res2_a);
    try testing.expectEqual(25, pure_res2_s);
    const show_pure2 = try pure_applied2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_pure2.deinit();
    try testing.expectEqual(45.14, show_pure2.a);
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, PutF 19, PutF 25, ", show_pure2.w.items);

    const pure_applied3 = try freem_monad.fapplyLam(u32, f64, pure_free_flam1, pure_free_a1);
    defer pure_applied3.deinit();
    const pure_state3 = try pure_applied3.foldFree(nat_statef_state, statef_functor, state_monad);
    const pure_res3_a, const pure_res3_s = try pure_state3.runState(13);
    _ = pure_state3.strongUnref();
    try testing.expectEqual(45.14, pure_res3_a);
    try testing.expectEqual(25, pure_res3_s);
    const show_pure3 = try pure_applied3.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_pure3.deinit();
    try testing.expectEqual(45.14, show_pure3.a);
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, PutF 19, PutF 25, ", show_pure3.w.items);

    // test all variants of FreeMonad StateF A with GetF operator
    const x_to_free_state = struct {
        const Error = FreeMonad(StateFCtor, u32).Error;
        fn xToFreeState(x: u64) Error!FreeMonad(StateFCtor, u32) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37 + x)) },
            };
            const a = @as(u32, @intCast(x)) * 2;
            return FreeMonad(StateFCtor, u32).freeM(allocator, a, @constCast(x_state_ops));
        }
    }.xToFreeState;

    const get_fn = struct {
        const Error = FreeMonad(StateFCtor, ExistType).Error;
        fn get(s: u64) Error!ExistType {
            return @intCast(s + 10);
        }
    }.get;

    var free_state = try FreeMonad(StateFCtor, u32).freeFOp(x_to_free_state, GetF, buildGetF(get_fn));
    defer free_state.deinit();
    const free_state1 = try freem_monad.fapply(u32, f64, pure_free_af1, free_state);
    defer free_state1.deinit();
    const state1 = try free_state1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res1_a, const res1_s = try state1.runState(13);
    _ = state1.strongUnref();
    // (17 + 10) * 2 + 3.14 = 57.14
    try testing.expectEqual(57.14, res1_a);
    // (17 + 10) + 37 = 64
    try testing.expectEqual(64, res1_s);
    const show_writer1 = try free_state1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer1.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer1.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, GetF, PutF 47, ", show_writer1.w.items);

    const free_state11 = try freem_monad.fapplyLam(u32, f64, pure_free_flam1, free_state);
    defer free_state11.deinit();
    const state11 = try free_state11.foldFree(nat_statef_state, statef_functor, state_monad);
    const res11_a, const res11_s = try state11.runState(13);
    _ = state11.strongUnref();
    // (17 + 10) * 2 + 3.14 = 57.14
    try testing.expectEqual(57.14, res11_a);
    // (17 + 10) + 37 = 64
    try testing.expectEqual(64, res11_s);
    const show_writer11 = try free_state11.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer11.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer11.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, GetF, PutF 47, ", show_writer11.w.items);

    const put_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
    };

    free_state = try free_state.appendFOps(allocator, put_ops);
    const free_state2 = try freem_monad.fapply(u32, f64, pure_free_af1, free_state);
    defer free_state2.deinit();
    const state2 = try free_state2.foldFree(nat_statef_state, statef_functor, state_monad);
    const res2_a, const res2_s = try state2.runState(13);
    _ = state2.strongUnref();
    // (37 + 10) * 2 + 3.14 = 97.14
    try testing.expectEqual(97.14, res2_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res2_s);
    const show_writer2 = try free_state2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer2.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer2.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, PutF 23, PutF 37, GetF, PutF 47, ", show_writer2.w.items);

    const free_state22 = try freem_monad.fapplyLam(u32, f64, pure_free_flam1, free_state);
    defer free_state22.deinit();
    const state22 = try free_state22.foldFree(nat_statef_state, statef_functor, state_monad);
    const res22_a, const res22_s = try state22.runState(13);
    _ = state22.strongUnref();
    // (37 + 10) * 2 + 3.14 = 97.14
    try testing.expectEqual(97.14, res22_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res22_s);
    const show_writer22 = try free_state22.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer22.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer22.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, PutF 23, PutF 37, GetF, PutF 47, ", show_writer22.w.items);

    const FnType1 = *const fn (u32) f64;
    const x_to_free_state_fn = struct {
        const Error = FreeMonad(StateFCtor, FnType1).Error;
        fn xToFreeState(x: u64) Error!FreeMonad(StateFCtor, FnType1) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(19 + x)) },
            };
            const res_fn = struct {
                fn f(a: u32) f64 {
                    return @as(f64, @floatFromInt(a)) + 6.18;
                }
            }.f;
            return FreeMonad(StateFCtor, FnType1).freeM(allocator, &res_fn, @constCast(x_state_ops));
        }
    }.xToFreeState;

    var free_state_af1 = try FreeMonad(StateFCtor, FnType1).freeFOp(x_to_free_state_fn, GetF, buildGetF(get_fn));
    defer free_state_af1.deinit();
    const free_state3 = try freem_monad.fapply(u32, f64, free_state_af1, free_state);
    defer free_state3.deinit();
    const state3 = try free_state3.foldFree(nat_statef_state, statef_functor, state_monad);
    const res3_a, const res3_s = try state3.runState(13);
    _ = state3.strongUnref();
    // (37 + 10) * 2 + 6.18 = 100.18
    try testing.expectEqual(100.18, res3_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res3_s);
    const show_writer3 = try free_state3.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer3.deinit();
    // (0 + 10) * 2 + 6.18 = 26.18
    try testing.expectEqual(26.18, show_writer3.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "GetF, PutF 29, PutF 23, PutF 37, GetF, PutF 47, ", show_writer3.w.items);

    const LamType1 = struct {
        _x: f64,
        const Self = @This();
        pub fn call(self: *const Self, a: u32) f64 {
            return @as(f64, @floatFromInt(a)) + self._x;
        }
    };
    const x_to_free_state_lam = struct {
        const Error = FreeMonad(StateFCtor, LamType1).Error;
        fn xToFreeState(x: u64) Error!FreeMonad(StateFCtor, LamType1) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(19 + x)) },
            };
            const res_lam = LamType1{ ._x = 6.18 };
            return FreeMonad(StateFCtor, LamType1).freeM(allocator, res_lam, @constCast(x_state_ops));
        }
    }.xToFreeState;

    var free_state_lam1 = try FreeMonad(StateFCtor, LamType1).freeFOp(x_to_free_state_lam, GetF, buildGetF(get_fn));
    defer free_state_lam1.deinit();
    const free_state33 = try freem_monad.fapplyLam(u32, f64, free_state_lam1, free_state);
    defer free_state33.deinit();
    const state33 = try free_state33.foldFree(nat_statef_state, statef_functor, state_monad);
    const res33_a, const res33_s = try state33.runState(13);
    _ = state33.strongUnref();
    // (37 + 10) * 2 + 6.18 = 100.18
    try testing.expectEqual(100.18, res33_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res33_s);
    const show_writer33 = try free_state33.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer33.deinit();
    // (0 + 10) * 2 + 6.18 = 26.18
    try testing.expectEqual(26.18, show_writer33.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "GetF, PutF 29, PutF 23, PutF 37, GetF, PutF 47, ", show_writer33.w.items);

    const put_af1_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(33)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(21)) },
    };
    free_state_af1 = try free_state_af1.appendFOps(allocator, put_af1_ops);
    const free_state4 = try freem_monad.fapply(u32, f64, free_state_af1, free_state);
    defer free_state4.deinit();
    const state4 = try free_state4.foldFree(nat_statef_state, statef_functor, state_monad);
    const res4_a, const res4_s = try state4.runState(13);
    _ = state4.strongUnref();
    // (37 + 10) * 2 + 6.18 = 100.18
    try testing.expectEqual(100.18, res4_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res4_s);
    const show_writer4 = try free_state4.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer4.deinit();
    // (0 + 10) * 2 + 6.18 = 26.18
    try testing.expectEqual(26.18, show_writer4.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(
        u8,
        "PutF 21, PutF 33, GetF, PutF 29, PutF 23, PutF 37, GetF, PutF 47, ",
        show_writer4.w.items,
    );

    var put_flam1_ops: [put_ops.len]FOpInfo = undefined;
    try free_state_af1.cloneFOpsToSlice(&put_flam1_ops);
    free_state_lam1 = try free_state_lam1.appendFOps(allocator, &put_flam1_ops);
    const free_state44 = try freem_monad.fapplyLam(u32, f64, free_state_lam1, free_state);
    defer free_state44.deinit();
    const state44 = try free_state44.foldFree(nat_statef_state, statef_functor, state_monad);
    const res44_a, const res44_s = try state44.runState(13);
    _ = state44.strongUnref();
    // (37 + 10) * 2 + 6.18 = 100.18
    try testing.expectEqual(100.18, res44_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res44_s);
    const show_writer44 = try free_state44.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer44.deinit();
    // (0 + 10) * 2 + 6.18 = 26.18
    try testing.expectEqual(26.18, show_writer44.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(
        u8,
        "PutF 21, PutF 33, GetF, PutF 29, PutF 23, PutF 37, GetF, PutF 47, ",
        show_writer44.w.items,
    );
}

///////////////////////////////////////////////////
// Definition of MWriter
///////////////////////////////////////////////////
fn MWriter(comptime W: type) TCtor {
    return struct {
        fn MWriterF(comptime A: type) type {
            return struct {
                a: A,
                w: W,

                const Self = @This();
                const BaseType = A;

                pub fn deinit(self: Self) void {
                    base.deinitOrUnref(self.w);
                }
            };
        }
    }.MWriterF;
}

pub fn tell(w: anytype) MWriter(@TypeOf(w))(void) {
    return .{ .a = {}, .w = w };
}

pub fn MWriterMonadImpl(comptime MonoidImpl: type, comptime W: type) type {
    return struct {
        monoid_impl: MonoidImpl,

        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = MWriter(W);

        /// Get base type of FreeMonad(F, A), it is must just is A.
        pub fn BaseType(comptime WriterWA: type) type {
            return WriterWA.BaseType;
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

        fn FaFnOrLamType(
            comptime K: MapFnKind,
            comptime M: FMapMode,
            comptime FnOrLam: type,
        ) type {
            if (M == .NormalMap) {
                return FaType(K, FnOrLam);
            } else {
                return FaLamType(K, FnOrLam);
            }
        }

        fn FbFnOrLamType(comptime M: FMapMode, comptime FnOrLam: type) type {
            if (M == .NormalMap) {
                return FbType(FnOrLam);
            } else {
                return FbLamType(FnOrLam);
            }
        }

        pub fn deinitFa(
            fa: anytype, // FreeMonad(F, A)
            comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
        ) void {
            free_fn(fa.a);
            fa.deinit();
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            _ = self;
            const B = MapFnRetType(@TypeOf(map_fn));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;

            const b = if (comptime isMapRef(K)) map_fn(&(fa.*.a)) else map_fn(fa.a);
            const _b = if (has_err) try b else b;
            if (isInplaceMap(K)) {
                base.deinitOrUnref(fa.a);
                return .{ .a = _b, .w = fa.w };
            } else {
                return .{ .a = _b, .w = try base.copyOrCloneOrRef(fa.w) };
            }
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            _ = self;
            const B = MapLamRetType(@TypeOf(map_lam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;

            const b = if (comptime isMapRef(K)) map_lam(@constCast(&(fa.*.a))) else map_lam(fa.a);
            const _b = if (has_err) try b else b;
            if (isInplaceMap(K)) {
                base.deinitOrUnref(fa.a);
                return .{ .a = _b, .w = fa.w };
            } else {
                return .{ .a = _b, .w = try base.copyOrCloneOrRef(fa.w) };
            }
        }

        pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
            const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
            _ = _A;
            const _a = if (has_err) try a else a;
            return .{ .a = _a, .w = try self.monoid_impl.mempty() };
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
            _ = _B;
            const f = ff.a;
            const _b = if (has_err) try f(fa.a) else f(fa.a);
            return .{ .a = _b, .w = try self.monoid_impl.mappend(ff.w, fa.w) };
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
            _ = _B;
            const lam = flam.a;
            const _b = if (has_err) try lam.call(fa.a) else lam.call(fa.a);
            return .{ .a = _b, .w = try self.monoid_impl.mappend(flam.w, fa.w) };
        }
        pub fn bind(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*Self, A) MbType(B),
        ) MbType(B) {
            const mb = try k(ma.a);
            return .{ .a = mb.a, .w = try self.monoid_impl.mappend(ma.w, mb.w) };
        }

        pub fn join(
            self: *Self,
            comptime A: type,
            mma: F(F(A)),
        ) MbType(A) {
            return .{ .a = mma.a.a, .w = try self.monoid_impl.mappend(mma.w, mma.a.w) };
        }
    };
}

///////////////////////////////////////////////////
// Definition of MWriterMaybe
///////////////////////////////////////////////////
/// The type is just MWriter(W, Maybe(A))
pub fn MWriterMaybe(comptime W: type) TCtor {
    return struct {
        fn MWriterMaybeF(comptime A: type) type {
            return struct {
                a: Maybe(A),
                w: W,

                const Self = @This();
                const BaseType = A;

                pub fn deinit(self: Self) void {
                    base.deinitOrUnref(self.w);
                }
            };
        }
    }.MWriterMaybeF;
}

pub fn MWriterMaybeMonadImpl(comptime MonoidImpl: type, comptime W: type) type {
    return struct {
        monoid_impl: MonoidImpl,

        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = MWriterMaybe(W);

        /// Get base type of FreeMonad(F, A), it is must just is A.
        pub fn BaseType(comptime WriterWA: type) type {
            return WriterWA.BaseType;
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
            if (fa.a) |_a| {
                free_fn(_a);
            }
            fa.deinit();
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            _ = self;
            const B = MapFnRetType(@TypeOf(map_fn));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;

            const _b = if (fa.a != null) blk_t: {
                const b = if (comptime isMapRef(K)) map_fn(&(fa.*.?.a)) else map_fn(fa.?.a);
                break :blk_t if (has_err) try b else b;
            } else null;
            if (isInplaceMap(K)) {
                if (fa.a) |_a| {
                    base.deinitOrUnref(_a);
                }
                return .{ .a = _b, .w = fa.w };
            } else {
                return .{ .a = _b, .w = try base.copyOrCloneOrRef(fa.w) };
            }
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            _ = self;
            const B = MapLamRetType(@TypeOf(map_lam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;

            const _b = if (fa.a != null) blk_t: {
                const b = if (comptime isMapRef(K))
                    map_lam.call(@constCast(&(fa.*.?.a)))
                else
                    map_lam.call(fa.?.a);
                break :blk_t if (has_err) try b else b;
            } else null;
            if (isInplaceMap(K)) {
                if (fa.a) |_a| {
                    base.deinitOrUnref(_a);
                }
                return .{ .a = _b, .w = fa.w };
            } else {
                return .{ .a = _b, .w = try base.copyOrCloneOrRef(fa.w) };
            }
        }

        pub fn pure(self: *Self, a: anytype) APaType(@TypeOf(a)) {
            const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
            _ = _A;
            const _a = if (has_err) try a else a;
            return .{ .a = _a, .w = try self.monoid_impl.mempty() };
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
            _ = _B;
            const f = ff.a;
            const _b = if (fa.a) |_a| blk_t: {
                break :blk_t if (has_err) try f(_a) else f(_a);
            } else null;
            return .{ .a = _b, .w = try self.monoid_impl.mappend(ff.w, fa.w) };
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
            _ = _B;
            const lam = flam.a;
            const _b = if (fa.a) |_a| blk_t: {
                break :blk_t if (has_err) try lam.call(_a) else lam.call(_a);
            } else null;
            return .{ .a = _b, .w = try self.monoid_impl.mappend(flam.w, fa.w) };
        }
        pub fn bind(
            self: *Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*Self, A) MbType(B),
        ) MbType(B) {
            const mb = if (ma.a) |_a|
                try k(self, _a)
            else
                .{ .a = null, .w = self.monoid_impl.mempty() };
            return .{ .a = mb.a, .w = try self.monoid_impl.mappend(ma.w, mb.w) };
        }

        pub fn join(
            self: *Self,
            comptime A: type,
            mma: F(F(A)),
        ) MbType(A) {
            if (mma.a) |_ma| {
                return .{ .a = _ma.a, .w = try self.monoid_impl.mappend(mma.w, _ma.w) };
            } else {
                return .{ .a = null, .w = try base.copyOrCloneOrRef(mma.w) };
            }
        }
    };
}

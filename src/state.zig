//! Definition of State struct, these is a instance of Functor|Applicative|Monad
//! typeclass.

const std = @import("std");
const base = @import("base.zig");
const monoid = @import("monoid.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const freetypes = @import("free_types.zig");
const maybe = @import("maybe.zig");
const arraym = @import("array_list_monad.zig");
const testu = @import("test_utils.zig");

const testing = std.testing;
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const Maybe = base.Maybe;
const ArrayList = std.ArrayList;

const TCtor = base.TCtor;
var maybe_error = maybe.maybe_error;

const MapFnInType = base.MapFnInType;
const MapFnRetType = base.MapFnRetType;
const MapLamInType = base.MapLamInType;
const MapLamRetType = base.MapLamRetType;

const ApplyFnInType = base.ApplyFnInType;
const ApplyFnRetType = base.ApplyFnRetType;
const ApplyLamInType = base.ApplyLamInType;
const ApplyLamRetType = base.ApplyLamRetType;

const FMapMode = base.FMapMode;
const MapFnKind = base.MapFnKind;
const isMapRef = base.isMapRef;
const isInplaceMap = base.isInplaceMap;
const isErrorUnionOrVal = base.isErrorUnionOrVal;
const EffectVal = base.EffectVal;

const Monoid = monoid.Monoid;
const Functor = functor.Functor;
const NatTrans = functor.NatTrans;
const Applicative = applicative.Applicative;
const Monad = monad.Monad;
const MonadFromImpl = monad.MonadFromImpl;
const ArrayListMonadImpl = arraym.ArrayListMonadImpl;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;
const FOpInfo = freetypes.FOpInfo;

const StateParentOp = enum {
    /// increace reference count of other state or object in state_parent
    inc_ref,
    /// decreace reference count of other state or object in state_parent
    dec_ref,
    /// free state_parent self
    free_self,
};

pub fn StateContext(comptime cfg: anytype) type {
    return struct {
        pub const ctx_cfg = cfg;
        pub const Error: ?type = ctx_cfg.errors;

        // the currying form of State function
        pub fn StateM(comptime S: type) TCtor {
            return struct {
                fn StateTCtor(comptime A: type) type {
                    return struct {
                        ref_count: u32,
                        // translate action lambda for State
                        trans_lam: TransLam,

                        const Self = @This();
                        pub const BaseType = A;
                        pub const StateS = S;
                        pub const StateA = A;
                        pub const StateAS = struct { A, S };
                        pub const TransLam = struct {
                            parent_op_fn: *const fn (self: *TransLam, op: StateParentOp) void,
                            trans_fn: *const fn (self: *TransLam, s: S) RetType,

                            const RetType = EffectVal(Error, StateAS);
                            // translate action function for State
                            pub inline fn call(trans_lam: *TransLam, s: S) RetType {
                                return trans_lam.trans_fn(trans_lam, s);
                            }
                        };
                        pub const free_s = ctx_cfg.free_s;
                        pub const FunctorImpl = StateMonadImpl(cfg, S);
                        pub const ApplicativeImpl = FunctorImpl;
                        pub const MonadImpl = FunctorImpl;

                        pub fn strongRef(state_self: *Self) *Self {
                            state_self.trans_lam.parent_op_fn(&state_self.trans_lam, .inc_ref);
                            state_self.ref_count += 1;
                            return state_self;
                        }

                        pub fn strongUnref(state_self: *Self) bool {
                            state_self.trans_lam.parent_op_fn(&state_self.trans_lam, .dec_ref);
                            if (state_self.ref_count > 1) {
                                state_self.ref_count -= 1;
                                return false;
                            }
                            state_self.ref_count = 0;
                            // free the parent struct of state struct
                            state_self.trans_lam.parent_op_fn(&state_self.trans_lam, .free_self);
                            return true;
                        }

                        /// This function run the function trans_fn in State(S, A) state,
                        /// and return result of trans_fn.
                        /// The parameter s is initial value of S for runState, this
                        /// functin should consume parameter s.
                        pub fn runState(state_self: *Self, s: S) EffectVal(Error, StateAS) {
                            const trans_lam = &state_self.trans_lam;
                            return trans_lam.call(s);
                        }
                    };
                }
            }.StateTCtor;
        }

        /// The State(S, A) is just a wrapper of lambda function with type S -> (A, S).
        pub fn State(comptime S: type, comptime A: type) type {
            return StateM(S)(A);
        }

        fn StateTypeFromLam(LamType: anytype) type {
            const S = MapLamInType(LamType);
            const RetType = MapLamRetType(LamType);
            const has_err, const TupleAS = isErrorUnionOrVal(RetType);
            _ = has_err;
            const tuple_info = @typeInfo(TupleAS);

            if (!(tuple_info == .@"struct" and
                tuple_info.@"struct".is_tuple and
                tuple_info.@"struct".fields.len == 2))
            {
                @compileError("Expect return type of lam is a 2-tuple, found '" ++
                    @typeName(TupleAS) ++ "'");
            }

            const A = tuple_info.@"struct".fields[0].type;
            comptime assert(S == tuple_info.@"struct".fields[1].type);
            return State(S, A);
        }

        /// Create a State from a lambda, this function will consume the parameter lam.
        pub fn mkStateFromLam(lam: anytype) EffectVal(Error, *StateTypeFromLam(@TypeOf(lam))) {
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

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, A).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, A), FromLamStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            base.deinitOrUnref(state_parent.trans_ctx.action_lam);
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        else => {},
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = EffectVal(Error, State(S, A).StateAS);
                fn f(trans_lam: *State(S, A).TransLam, input_s: S) RetType {
                    ctx_cfg.free_s(ctx_cfg.allocator, input_s);
                    const state_parent = getStateParentByTransLam(State(S, A), FromLamStateType, trans_lam);
                    const trans_ctx: TransCtx = state_parent.trans_ctx;
                    return trans_ctx.action_lam.call(input_s);
                }
            }.f;

            var const_state = try ctx_cfg.allocator.create(FromLamStateType);
            const_state.state.ref_count = 1;
            const_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            const_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            const_state.trans_ctx.action_lam = lam;
            return &const_state.state;
        }

        pub fn mkConstantState(comptime S: type, comptime A: type, s: S, a: A) EffectVal(Error, *State(S, A)) {
            const TransCtx = struct {
                local_s: ?S,
                local_a: A,
            };

            const ConstStateType = struct {
                state: State(S, A),
                trans_ctx: TransCtx,
            };

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, A).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, A), ConstStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            if (state_parent.trans_ctx.local_s) |local_s| {
                                ctx_cfg.free_s(ctx_cfg.allocator, local_s);
                            }
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        else => {},
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = EffectVal(Error, State(S, A).StateAS);
                fn f(trans_lam: *State(S, A).TransLam, input_s: S) RetType {
                    ctx_cfg.free_s(ctx_cfg.allocator, input_s);
                    const state_parent = getStateParentByTransLam(State(S, A), ConstStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    defer trans_ctx.local_s = null;
                    return .{ trans_ctx.local_a, trans_ctx.local_s.? };
                }
            }.f;

            var const_state = try ctx_cfg.allocator.create(ConstStateType);
            const_state.state.ref_count = 1;
            const_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            const_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            const_state.trans_ctx.local_s = s;
            const_state.trans_ctx.local_a = a;
            return &const_state.state;
        }

        pub fn get(comptime S: type) EffectVal(Error, *State(S, S)) {
            const GetStateType = struct {
                state: State(S, S),
            };

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, S).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, S), GetStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        else => {},
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = EffectVal(Error, struct { S, S });
                fn f(trans_lam: *State(S, S).TransLam, s: S) RetType {
                    _ = trans_lam;
                    return .{ try ctx_cfg.clone_s(s), s };
                }
            }.f;

            var get_state = try ctx_cfg.allocator.create(GetStateType);
            get_state.state.ref_count = 1;
            get_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            get_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            return &get_state.state;
        }

        pub fn put(comptime S: type, s: S) EffectVal(Error, *State(S, void)) {
            const TransCtx = struct {
                local_s: ?S,
            };

            const PutStateType = struct {
                state: State(S, void),
                trans_ctx: TransCtx,
            };

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, void).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, void), PutStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            if (state_parent.trans_ctx.local_s) |local_s| {
                                ctx_cfg.free_s(ctx_cfg.allocator, local_s);
                            }
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        else => {},
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = EffectVal(Error, struct { void, S });
                fn f(trans_lam: *State(S, void).TransLam, input_s: S) RetType {
                    ctx_cfg.free_s(ctx_cfg.allocator, input_s);
                    const state_parent = getStateParentByTransLam(State(S, void), PutStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    defer trans_ctx.local_s = null;
                    return .{ {}, trans_ctx.local_s.? };
                }
            }.f;
            var put_state = try ctx_cfg.allocator.create(PutStateType);
            put_state.state.ref_count = 1;
            put_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            put_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            put_state.trans_ctx.local_s = s;
            return &put_state.state;
        }
    };
}

fn getStateParentByTransLam(
    comptime StateType: type,
    comptime StateParent: type,
    trans_lam: anytype,
) *StateParent {
    return @alignCast(@fieldParentPtr("state", @as(*StateType, @fieldParentPtr("trans_lam", trans_lam))));
}

pub fn CloneStateSFn(comptime S: type) type {
    return *const fn (a: S) Allocator.Error!S;
}

pub fn FreeStateSFn(comptime S: type) type {
    return *const fn (Allocator, a: S) void;
}

pub fn StateCtxCfg(comptime S: type) type {
    return struct {
        allocator: Allocator,
        clone_s: CloneStateSFn(S),
        free_s: FreeStateSFn(S),
        errors: ?type,
    };
}

fn getCopyAsClone(comptime S: type) CloneStateSFn(S) {
    return struct {
        fn f(a: S) Allocator.Error!S {
            return a;
        }
    }.f;
}

fn getFreeNothing(comptime S: type) FreeStateSFn(S) {
    return struct {
        fn f(allocator: Allocator, a: S) void {
            _ = allocator;
            _ = a;
        }
    }.f;
}

fn getDefaultStateCfg(comptime S: type, allocator: Allocator) StateCtxCfg(S) {
    return .{
        .clone_s = getCopyAsClone(S),
        .free_s = getFreeNothing(S),
        .allocator = allocator,
        .errors = Allocator.Error,
    };
}

fn getNormalClone(comptime S: type) CloneStateSFn(S) {
    return struct {
        fn f(a: S) Allocator.Error!S {
            return a.clone();
        }
    }.f;
}

fn getFreeOneT(comptime S: type) FreeStateSFn(S) {
    return struct {
        fn f(allocator: Allocator, a: S) void {
            allocator.destroy(a);
        }
    }.f;
}

fn getDeinitOneT(comptime S: type) FreeStateSFn(S) {
    return struct {
        fn f(allocator: Allocator, a: S) void {
            _ = allocator;
            a.deinit();
        }
    }.f;
}

pub fn getDeinitCfg(comptime S: type, allocator: Allocator) StateCtxCfg(S) {
    return .{
        .clone_s = getNormalClone(S),
        .free_s = getDeinitOneT(S),
        .allocator = allocator,
        .errors = Allocator.Error,
    };
}

test "get s from (State s a)" {
    const allocator = testing.allocator;
    const DefaultCtx = StateContext(comptime getDefaultStateCfg(i32, allocator));
    var state = try DefaultCtx.get(i32);
    defer _ = state.strongUnref();
    const res_a, const res_s = try state.runState(42);
    try testing.expectEqual(42, res_a);
    try testing.expectEqual(42, res_s);
}

test "put s to (State s a)" {
    const allocator = testing.allocator;
    const DefaultCtx = StateContext(comptime getDefaultStateCfg(i32, allocator));
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

        pub const Error: ?type = maybe_error.mappend(Allocator.Error, cfg.errors);

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
            fa: anytype, // State(S, A)
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
            const RetE = Error.? || if (has_err) info.error_union.error_set else error{};
            return RetE!struct { _A, RetS };
        }

        pub fn fmap(
            self: *const Self,
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

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, _B).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, _B), FmapStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        .inc_ref => {
                            _ = state_parent.trans_ctx.local_state.strongRef();
                        },
                        .dec_ref => {
                            _ = state_parent.trans_ctx.local_state.strongUnref();
                        },
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const state_parent = getStateParentByTransLam(State(S, _B), FmapStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const a, const s = try trans_ctx.local_state.runState(input_s);
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
            fmap_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
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

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, _B).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, _B), FmapLamStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        .inc_ref => {
                            _ = state_parent.trans_ctx.local_state.strongRef();
                        },
                        .dec_ref => {
                            _ = state_parent.trans_ctx.local_state.strongUnref();
                        },
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const state_parent = getStateParentByTransLam(State(S, _B), FmapLamStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const a, const s = try trans_ctx.local_state.runState(input_s);
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
            fmaplam_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            fmaplam_state.trans_ctx.map_lam = map_lam;
            fmaplam_state.trans_ctx.local_state = fa.strongRef();
            return &fmaplam_state.state;
        }

        pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
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

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, _A).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, _A), PureStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        .inc_ref => {
                            _ = base.tryStrongRef(state_parent.trans_ctx.local_a);
                        },
                        .dec_ref => {
                            base.tryStrongUnref(state_parent.trans_ctx.local_a);
                        },
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, A);
                fn f(trans_lam: *State(S, _A).TransLam, input_s: S) RetType {
                    const state_parent = getStateParentByTransLam(State(S, _A), PureStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    return .{ trans_ctx.local_a, input_s };
                }
            }.f;

            var pure_state = try ctx_cfg.allocator.create(PureStateType);
            pure_state.state.ref_count = 1;
            pure_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            pure_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            pure_state.trans_ctx.local_a = base.tryStrongRef(_a);
            return &pure_state.state;
        }

        pub fn fapply(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            // ff: F(*const fn (A) B),
            ff: anytype,
            fa: F(ApplyFnInType(Self, @TypeOf(ff))),
        ) AFbType(ApplyFnRetType(Self, @TypeOf(ff))) {
            _ = self;
            const A = ApplyFnInType(Self, @TypeOf(ff));
            const B = ApplyFnRetType(Self, @TypeOf(ff));
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

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, _B).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, _B), FapplyStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        .inc_ref => {
                            _ = state_parent.trans_ctx.local_state_f.strongRef();
                            _ = state_parent.trans_ctx.local_state.strongRef();
                        },
                        .dec_ref => {
                            _ = state_parent.trans_ctx.local_state_f.strongUnref();
                            _ = state_parent.trans_ctx.local_state.strongUnref();
                        },
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const state_parent = getStateParentByTransLam(State(S, _B), FapplyStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
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

            var fapply_state = try ctx_cfg.allocator.create(FapplyStateType);
            fapply_state.state.ref_count = 1;
            fapply_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            fapply_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            fapply_state.trans_ctx.local_state_f = ff.strongRef();
            fapply_state.trans_ctx.local_state = fa.strongRef();
            return &fapply_state.state;
        }

        pub fn fapplyLam(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(ApplyLamInType(Self, @TypeOf(flam))),
        ) AFbType(ApplyLamRetType(Self, @TypeOf(flam))) {
            _ = self;
            const A = ApplyLamInType(Self, @TypeOf(flam));
            const B = ApplyLamRetType(Self, @TypeOf(flam));
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

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, _B).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, _B), FapplyLamStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        .inc_ref => {
                            _ = state_parent.trans_ctx.local_state_flam.strongRef();
                            _ = state_parent.trans_ctx.local_state.strongRef();
                        },
                        .dec_ref => {
                            _ = state_parent.trans_ctx.local_state_flam.strongUnref();
                            _ = state_parent.trans_ctx.local_state.strongUnref();
                        },
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, _B).TransLam, input_s: S) RetType {
                    const state_parent = getStateParentByTransLam(State(S, _B), FapplyLamStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const alam, const s1 = try trans_ctx.local_state_flam.runState(input_s);
                    const a, const s2 = try trans_ctx.local_state.runState(s1);
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
            fapplylam_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            fapplylam_state.trans_ctx.local_state_flam = flam.strongRef();
            fapplylam_state.trans_ctx.local_state = fa.strongRef();
            return &fapplylam_state.state;
        }

        pub fn bind(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*const Self, A) MbType(B),
        ) MbType(B) {
            const TransCtx = struct {
                // a pointer of state monad instance
                monad_impl: *const Self,
                // a local temporary state value for ma
                local_state: *State(S, A),
                // a local temporary continuation function of bind function
                local_k: @TypeOf(k),
            };

            const BindStateType = struct {
                state: State(S, B),
                trans_ctx: TransCtx,
            };

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, B).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, B), BindStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        .inc_ref => {
                            _ = state_parent.trans_ctx.local_state.strongRef();
                        },
                        .dec_ref => {
                            _ = state_parent.trans_ctx.local_state.strongUnref();
                        },
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, B);
                fn f(trans_lam: *State(S, B).TransLam, input_s: S) RetType {
                    const state_parent = getStateParentByTransLam(State(S, B), BindStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const a, const s = try trans_ctx.local_state.runState(input_s);
                    const state = try trans_ctx.local_k(trans_ctx.monad_impl, a);
                    const out_a, const out_s = try state.runState(s);
                    _ = state.strongUnref();
                    return .{ out_a, out_s };
                }
            }.f;

            var bind_state = try ctx_cfg.allocator.create(BindStateType);
            bind_state.state.ref_count = 1;
            bind_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            bind_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            bind_state.trans_ctx.monad_impl = self;
            bind_state.trans_ctx.local_state = ma.strongRef();
            bind_state.trans_ctx.local_k = k;
            return &bind_state.state;
        }

        pub fn join(
            self: *const Self,
            comptime A: type,
            mma: F(F(A)),
        ) MbType(A) {
            const TransCtx = struct {
                // a pointer of state monad instance
                monad_impl: *const Self,
                // a local temporary state value for mma
                local_state: *State(S, *State(S, A)),
            };

            const JoinStateType = struct {
                state: State(S, A),
                trans_ctx: TransCtx,
            };

            const parent_op_fn = struct {
                fn stateParentOp(trans_lam: *State(S, A).TransLam, op: StateParentOp) void {
                    const state_parent = getStateParentByTransLam(State(S, A), JoinStateType, trans_lam);
                    switch (op) {
                        .free_self => {
                            ctx_cfg.allocator.destroy(state_parent);
                        },
                        .inc_ref => {
                            _ = state_parent.trans_ctx.local_state.strongRef();
                        },
                        .dec_ref => {
                            _ = state_parent.trans_ctx.local_state.strongUnref();
                        },
                    }
                }
            }.stateParentOp;

            const trans_fn = struct {
                const RetType = TransFnRetType(S, A);
                fn f(trans_lam: *State(S, A).TransLam, input_s: S) RetType {
                    const state_parent = getStateParentByTransLam(State(S, A), JoinStateType, trans_lam);
                    const trans_ctx: *TransCtx = &state_parent.trans_ctx;
                    const state, const s = try trans_ctx.local_state.runState(input_s);
                    const out_a, const out_s = try state.runState(s);
                    _ = state.strongUnref();
                    return .{ out_a, out_s };
                }
            }.f;

            var join_state = try ctx_cfg.allocator.create(JoinStateType);
            join_state.state.ref_count = 1;
            join_state.state.trans_lam.trans_fn = @constCast(&trans_fn);
            join_state.state.trans_lam.parent_op_fn = @constCast(&parent_op_fn);
            join_state.trans_ctx.monad_impl = self;
            join_state.trans_ctx.local_state = mma.strongRef();
            return &join_state.state;
        }
    };
}

const FunctorImplFromTCtor = functor.FunctorImplFromTCtor;
const ApplicativeImplFromTCtor = functor.ApplicativeImplFromTCtor;
const MonadImplFromTCtor = functor.MonadImplFromTCtor;

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
    const default_cfg = comptime getDefaultStateCfg(u32, allocator);
    const DefaultCtx = StateContext(default_cfg);
    const StateU32 = DefaultCtx.StateM(u32);
    const StateFunctor = Functor(StateU32);
    const state_functor = StateFunctor.InstanceImpl{ .allocator = allocator };

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
    const StateArrayU32 = ArrayStCtx.StateM(ArrayListU32);
    _ = Functor(StateArrayU32);
    var array_st_functor = FunctorImplFromTCtor(StateArrayU32){ .allocator = allocator };

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
    const default_cfg = comptime getDefaultStateCfg(u32, allocator);
    const DefaultCtx = StateContext(default_cfg);
    const StateU32 = DefaultCtx.StateM(u32);
    const StateApplicative = Applicative(StateU32);
    const state_applicative = StateApplicative.InstanceImpl{ .allocator = allocator };

    var state_a = try state_applicative.pure(@as(u32, 13));
    defer _ = state_a.strongUnref();
    const pured_a, const pured_s = try state_a.runState(42);
    try testing.expectEqual(13, pured_a);
    try testing.expectEqual(42, pured_s);

    // the comptime function must be a const function pointer
    const add_pi_f64_p: *const @TypeOf(add_pi_f64) = add_pi_f64;
    var state_f = try state_applicative.pure(add_pi_f64_p);
    defer _ = state_f.strongUnref();
    var state_b = try state_applicative.fapply(state_f, state_a);
    defer _ = state_b.strongUnref();
    var res1_a, var res1_s = try state_b.runState(42);
    try testing.expectEqual(16.14, res1_a);
    try testing.expectEqual(42, res1_s);

    const add_x_f64_lam = Add_x_f64_Lam{ ._x = 3.14 };
    var state_lam = try state_applicative.pure(add_x_f64_lam);
    defer _ = state_lam.strongUnref();
    var state_c = try state_applicative.fapplyLam(state_lam, state_a);
    defer _ = state_c.strongUnref();
    res1_a, res1_s = try state_c.runState(42);
    try testing.expectEqual(16.14, res1_a);
    try testing.expectEqual(42, res1_s);
}

test "State(s, a) Monad bind" {
    // test State(u32, a)
    const allocator = testing.allocator;
    const default_cfg = comptime getDefaultStateCfg(u32, allocator);
    const DefaultCtx = StateContext(default_cfg);
    const StateU32 = DefaultCtx.StateM(u32);
    const StateMonad = Monad(StateU32);
    const state_monad = StateMonad.InstanceImpl{ .allocator = allocator };

    var state_a = try state_monad.pure(@as(u32, 13));
    defer _ = state_a.strongUnref();
    const pured_a, const pured_s = try state_a.runState(42);
    try testing.expectEqual(13, pured_a);
    try testing.expectEqual(42, pured_s);

    var state_binded = try state_monad.bind(u32, f64, state_a, struct {
        fn f(inst: *const @TypeOf(state_monad), a: u32) StateMonad.MbType(f64) {
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
    const ArrayMonad = Monad(ArrayList);
    const array_monad = ArrayMonad.InstanceImpl{ .allocator = allocator };

    const array_cfg = comptime getDeinitCfg(ArrayList(i32), allocator);
    const ArrayStCtx = StateContext(array_cfg);
    const StateArrayI32 = ArrayStCtx.StateM(ArrayList(i32));
    const StateMonad = Monad(StateArrayI32);
    const state_array_monad = StateMonad.InstanceImpl{ .allocator = allocator };
    const ArrayStImpl = @TypeOf(state_array_monad);

    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: ArrayStImpl,
        arrayl_monad: ArrayListMonadImpl,
        param1: i32,

        // intermediate variable
        as: ?ArrayList(i32) = null,
        b: u32 = undefined,

        const Ctx = @This();
        pub const Error: ?type = ArrayStImpl.Error;

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
    }{ .monad_impl = state_array_monad, .arrayl_monad = array_monad, .param1 = input1 };
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
                putf: struct { S, A },
                getf: *GetfLamType,

                const Self = @This();
                const GetfLamType = base.ComposableLam(cfg, S, EffectVal(Error, A));
                pub const BaseType = A;
                pub const Error: ?type = cfg.errors;
                pub const ExistentialType = S;
                pub const OpCtorDefs = ValidateOpCtorDefs();
                pub const StateS = S;
                pub const StateA = A;

                pub const FunctorImpl = StateFFunctorImpl(cfg, S);

                fn ValidateOpCtorDefs() type {
                    const op_ctor_defs = StateFCtorDefs(cfg, S, A);
                    const CtorEnum = std.meta.DeclEnum(op_ctor_defs);
                    const putf_e = @intFromEnum(std.meta.activeTag(Self{ .putf = undefined }));
                    const getf_e = @intFromEnum(std.meta.activeTag(Self{ .getf = undefined }));
                    // Check if it has same order between PutF and putf
                    assert(@intFromEnum(CtorEnum.PutF) == putf_e);
                    assert(@intFromEnum(CtorEnum.GetF) == getf_e);
                    return op_ctor_defs;
                }

                pub fn effGetFfromFn(get_fn: *const fn (S) EffectVal(Error, A)) EffectVal(Error, Self) {
                    return .{ .getf = try GetfLamType.createByFn(get_fn) };
                }

                pub fn effPutF(s: S, a: A) Self {
                    return .{ .putf = .{ s, a } };
                }

                pub fn deinit(self: Self) void {
                    if (self == .getf) {
                        _ = self.getf.strongUnref();
                    } else {
                        base.deinitOrUnref(self.putf[0]);
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
        pub fn BaseType(comptime StateSA: type) type {
            return StateSA.BaseType;
        }

        pub const Error: ?type = maybe_error.mappend(Allocator.Error, cfg.errors);

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

        pub fn fmap(
            self: *const Self,
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

            if (_fa == .getf) {
                const getf = if (isInplaceMap(K)) fa.getf else fa.getf.strongRef();
                if (comptime isMapRef(K)) {
                    const map_ref_lam = MapRefLam{ .map_fn = map_fn };
                    return .{ .getf = try getf.appendLam(map_ref_lam) };
                }
                return .{ .getf = try getf.appendFn(map_fn) };
            } else {
                const b = if (comptime isMapRef(K))
                    map_fn(&fa.putf[1])
                else
                    map_fn(fa.putf[1]);
                const _b = if (has_err) try b else b;
                return .{ .putf = .{ fa.putf[0], _b } };
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

            if (_fa == .getf) {
                const getf = if (isInplaceMap(K)) fa.getf else fa.getf.strongRef();
                if (comptime isMapRef(K)) {
                    const map_ref_lam = MapRefLam{ .map_lam = map_lam };
                    return .{ .getf = try getf.appendLam(map_ref_lam) };
                }
                return .{ .getf = try getf.appendLam(map_lam) };
            } else {
                const b = if (comptime isMapRef(K))
                    map_lam.call(&fa.putf[1])
                else
                    map_lam.call(fa.putf[1]);
                const _b = if (has_err) try b else b;
                return .{ .putf = .{ fa.putf[0], _b } };
            }
        }
    };
}

/// All value constructors for StateF Functor
fn StateFCtorDefs(comptime cfg: anytype, comptime S: type, comptime A: type) type {
    const Error = cfg.errors;

    // Define Op constructor lambdas for StateF
    return struct {
        // The order of PutF and GetF must be same as order of putf and getf in StateF
        pub const PutF = PutFLam;
        pub const GetF = GetFLam;

        const SelfCtor = @This();
        const CtorEnum = std.meta.DeclEnum(SelfCtor);
        const PutF_E: FOpEnumInt = @intFromEnum(CtorEnum.PutF);
        const GetF_E: FOpEnumInt = @intFromEnum(CtorEnum.GetF);

        const PutFLam = extern struct {
            lam_ctx: ?*S = null,

            const Self = @This();
            pub fn build(s: S) EffectVal(Error, Self) {
                const put_s = try cfg.allocator.create(S);
                put_s.* = try base.copyOrCloneOrRef(s);
                return .{ .lam_ctx = put_s };
            }

            pub fn fpureToFreem(FreeMType: type, fpure: StateFA(cfg, S, A)) EffectVal(Error, FreeMType) {
                const ops_array = [_]FOpInfo{
                    .{ .op_e = PutF_E, .op_lam = @bitCast(try build(fpure.putf[0])) },
                };
                const a = fpure.putf[1].pure_m;
                return FreeMType.freeM(a, @constCast(&ops_array));
            }

            pub fn deinit(self: Self) void {
                if (self.lam_ctx != null) {
                    base.deinitOrUnref(self.lam_ctx.?.*);
                    cfg.allocator.destroy(self.lam_ctx.?);
                }
            }

            pub fn clone(self: Self) EffectVal(Error, Self) {
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

                return .{ .putf = .{ self.lam_ctx.?.*, a } };
            }
        };

        const GetFLam = struct {
            // composable function
            lam_ctx: *GetfLamType,

            const Self = @This();
            // This Op is just a function that return type is A
            pub const is_fn_op = true;
            const GetfLamType = base.ComposableLam(cfg, S, EffectVal(Error, A));

            /// build GetF from function or lambda
            pub fn build(action: anytype) EffectVal(Error, Self) {
                const info = @typeInfo(@TypeOf(action));
                const is_valid, const action_lam = switch (info) {
                    .@"struct" => .{ true, action },

                    .@"fn" => .{ true, base.mapFnToLam(action) },
                    .pointer => if (@typeInfo(info.pointer.child) == .@"fn")
                        .{ true, base.mapFnToLam(action) }
                    else
                        .{ false, undefined },
                    else => .{ false, undefined },
                };

                if (!is_valid) {
                    @compileError("Expect action be a function or lambda," ++
                        " found '" ++ @typeName(@TypeOf(action)) ++ "'");
                }

                const getf_lam = try GetfLamType.create(action_lam);
                return .{ .lam_ctx = getf_lam };
            }

            pub fn fpureToFreem(FreeMType: type, fpure: StateFA(cfg, S, A)) EffectVal(Error, FreeMType) {
                comptime assert(S == FreeMType.ExistType);
                const impureId = base.getEffectIdentityFn(Error, S);
                const getf_lam = try base.ComposableLam(cfg, S, EffectVal(Error, S)).createByFn(impureId);
                return FreeMType.freeFOp(fpure.getf, GetF_E, .{ .lam_ctx = getf_lam });
            }

            pub fn deinit(self: Self) void {
                _ = self.lam_ctx.strongUnref();
            }

            pub fn clone(self: Self) EffectVal(Error, Self) {
                return .{ .lam_ctx = self.lam_ctx.strongRef() };
            }

            pub fn call(self: *const Self) EffectVal(Error, StateFA(cfg, S, A)) {
                return StateFA(cfg, S, A){ .getf = self.lam_ctx.strongRef() };
            }
        };
    };
}

pub fn liftPutF(
    comptime cfg: anytype,
    s: anytype,
    a: anytype,
) !FreeMonad(cfg, StateF(cfg, @TypeOf(s)), @TypeOf(a)) {
    const S = @TypeOf(s);
    const A = @TypeOf(a);
    const F = StateF(cfg, S);

    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, S, A));
    const PutF: FOpEnumInt = @intFromEnum(StateFCtorEnum.PutF);
    const buildPutF = StateFCtorDefs(cfg, S, A).PutF.build;
    const put_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(s)) },
    };
    return FreeMonad(cfg, F, u32).freeM(a, @constCast(put_ops));
}

fn LiftGetFType(comptime cfg: anytype, comptime ActionType: type) type {
    const info = @typeInfo(ActionType);
    switch (info) {
        .@"struct" => {
            const S = MapLamInType(ActionType);
            const A = MapLamRetType(ActionType);
            const has_err, const _A = isErrorUnionOrVal(A);
            _ = has_err;
            return FreeMonad(cfg, StateF(cfg, S), _A);
        },

        .@"fn" => {
            const S = MapFnInType(ActionType);
            const A = MapFnRetType(ActionType);
            const has_err, const _A = isErrorUnionOrVal(A);
            _ = has_err;
            return FreeMonad(cfg, StateF(cfg, S), _A);
        },
        .pointer => if (@typeInfo(info.pointer.child) == .@"fn") {
            const S = MapFnInType(ActionType);
            const A = MapFnRetType(ActionType);
            const has_err, const _A = isErrorUnionOrVal(A);
            _ = has_err;
            return FreeMonad(cfg, StateF(cfg, S), _A);
        } else {
            @compileError("Expect a type of function or lambda," ++
                " found '" ++ @typeName(ActionType) ++ "'");
        },
        else => {
            @compileError("Expect a type of function or lambda," ++
                " found '" ++ @typeName(ActionType) ++ "'");
        },
    }
}

pub fn liftGetF(
    comptime cfg: anytype,
    action: anytype,
) !LiftGetFType(cfg, @TypeOf(action)) {
    const info = @typeInfo(@TypeOf(action));
    const is_valid, const action_lam = switch (info) {
        .@"struct" => .{ true, action },

        .@"fn" => .{ true, base.mapFnToLam(action) },
        .pointer => if (@typeInfo(info.pointer.child) == .@"fn")
            .{ true, base.mapFnToLam(action) }
        else
            .{ false, undefined },
        else => .{ false, undefined },
    };

    if (!is_valid) {
        @compileError("Expect action be a function or lambda," ++
            " found '" ++ @typeName(@TypeOf(action)) ++ "'");
    }

    const Error = cfg.errors;
    const S = MapLamInType(@TypeOf(action_lam));
    const A = MapLamRetType(@TypeOf(action_lam));
    const has_err, const _A = isErrorUnionOrVal(A);
    _ = has_err;
    const F = StateF(cfg, S);
    const ExistType = freetypes.GetExistentialType(F);
    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, S, _A));
    const GetF: FOpEnumInt = @intFromEnum(StateFCtorEnum.GetF);
    const buildGetF = StateFCtorDefs(cfg, S, ExistType).GetF.build;

    const comp_action_lam = try base.ComposableLam(cfg, S, A).create(action_lam);
    const getf_lam = try comp_action_lam.appendFn(FreeMonad(cfg, F, _A).pureM);
    defer _ = getf_lam.strongUnref();
    return FreeMonad(cfg, F, _A).freeFOp(getf_lam, GetF, try buildGetF(base.getEffectIdentityFn(Error, S)));
}

test "FreeMonad(StateF, A) liftFree" {
    const allocator = testing.allocator;
    const StateS = u64;
    const cfg = getDefaultStateCfg(StateS, allocator);
    const F = StateF(cfg, StateS);
    const StateFFunctor = Functor(F);
    const statef_functor = StateFFunctor.InstanceImpl{ .allocator = allocator };

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = MonadFromImpl(ShowMonadImpl);
    const ArrayMonoid = Monoid(ArrayList(u8));
    const array_monoid = ArrayMonoid.InstanceImpl{ .allocator = allocator };
    const show_monad = ShowMonad.InstanceImpl{ .monoid_impl = array_monoid };
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.InstanceImpl{ .allocator = allocator };

    const s: StateS = 17;
    const a: u32 = 42;
    const statef1 = StateFA(cfg, StateS, u32){ .putf = .{ s, a } };
    const free_state1 = try FreeMonad(cfg, F, u32).liftFree(&statef_functor, statef1);
    // const free_state1 = try liftPutF(cfg, s, a);
    defer free_state1.deinit();
    const show1_writer = try free_state1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show1_writer.deinit();
    try testing.expectEqual(42, show1_writer.a);
    try testing.expectEqualSlices(u8, "PutF 17, ", show1_writer.w.items);

    const get_fn = struct {
        const Error = cfg.errors;
        fn get(get_s: u64) EffectVal(Error, u32) {
            return @intCast(get_s + 10);
        }
    }.get;
    const statef2 = try StateFA(cfg, StateS, u32).effGetFfromFn(get_fn);
    defer statef2.deinit();
    const free_state2 = try FreeMonad(cfg, F, u32).liftFree(&statef_functor, statef2);
    // const free_state2 = try liftGetF(cfg, get_fn);
    defer free_state2.deinit();
    const show2_writer = try free_state2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show2_writer.deinit();
    try testing.expectEqual(10, show2_writer.a);
    try testing.expectEqualSlices(u8, "GetF, ", show2_writer.w.items);
}

pub fn StateFToStateNatImpl(comptime cfg: anytype, comptime S: type) type {
    const DefaultCtx = StateContext(cfg);
    return struct {
        const Self = @This();

        pub const F = StateF(cfg, S);
        pub const G = StateMonadImpl(cfg, S).F;
        pub const Error: ?type = Allocator.Error;

        pub fn trans(self: Self, comptime A: type, fa: F(A)) Error.?!G(A) {
            _ = self;
            if (fa == .putf) {
                // fa.putf is tuple of (S, State(S, A))
                // It is just as Haskell code:
                //     State $ \s -> (PutF.a, PutF.s)
                return DefaultCtx.mkConstantState(S, A, fa.putf[0], fa.putf[1]);
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
                    ) EffectVal(DefaultCtx.Error, DefaultCtx.State(S, A).StateAS) {
                        // This lambda just as Haskell code:
                        //     \s -> (GetF.g s, s)
                        return .{ try lam_self.local_fa.getf.call(s), s };
                    }
                }{ .local_fa = .{ .getf = fa.getf.strongRef() } };
                // It is just as Haskell code:
                //     State $ \s -> (GetF.g s, s)
                return DefaultCtx.mkStateFromLam(action_lam);
            }
        }
    };
}

pub fn StateFShowNatImpl(comptime cfg: anytype, comptime S: type) type {
    const InF = StateF(cfg, S);
    const ExistType = freetypes.GetExistentialType(InF);
    return struct {
        allocator: Allocator,

        const Self = @This();

        pub const F = InF;
        pub const G = MWriterMaybe(ArrayList(u8));
        pub const Error: ?type = Allocator.Error;

        pub fn trans(self: Self, comptime A: type, fa: F(A)) Error.?!G(A) {
            if (fa == .putf) {
                const put_fmt_str = "PutF {any}, ";
                const len: usize = @intCast(std.fmt.count(put_fmt_str, .{fa.putf[0]}));
                var array = try ArrayList(u8).initCapacity(self.allocator, len);
                const put_buf = array.addManyAsSliceAssumeCapacity(len);
                _ = std.fmt.bufPrint(put_buf, put_fmt_str, .{fa.putf[0]}) catch |err|
                    switch (err) {
                        error.NoSpaceLeft => unreachable, // we just counted the size above
                    };
                return .{ .a = fa.putf[1], .w = array };
            } else {
                const get_str = "GetF, ";
                var array = try ArrayList(u8).initCapacity(self.allocator, get_str.len);
                array.appendSliceAssumeCapacity(get_str);
                const init_val = base.defaultVal(ExistType);
                return .{ .a = try fa.getf.call(init_val), .w = array };
            }
        }
    };
}

fn statefToA(
    comptime cfg: anytype,
    comptime S: type,
    comptime A: type,
) *const fn (a: StateFA(cfg, S, A)) A {
    const F = StateF(cfg, S);
    const ExistType = freetypes.GetExistentialType(F);
    return struct {
        fn iterFn(statef: StateFA(cfg, S, A)) A {
            switch (statef) {
                .getf => {
                    const init_val = base.defaultVal(ExistType);
                    return statef.getf.call(init_val) catch base.defaultVal(A);
                },
                .putf => {
                    return statef.putf[1];
                },
            }
        }
    }.iterFn;
}

const ArrayListMonoidImpl = arraym.ArrayListMonoidImpl;
const FreeMonad = freetypes.FreeMonad;
const FreeMonadImpl = freetypes.FreeMonadImpl;
const FOpEnumInt = freetypes.FOpEnumInt;

test "FreeMonad(StateF, A) foldFree and iter" {
    const allocator = testing.allocator;
    const StateS = u64;
    const cfg = getDefaultStateCfg(StateS, allocator);
    const F = StateF(cfg, StateS);
    const StateFFunctor = Functor(F);
    const statef_functor = StateFFunctor.InstanceImpl{ .allocator = allocator };

    const StateU64 = StateContext(cfg).StateM(StateS);
    const StateMonad = Monad(StateU64);
    const state_monad = StateMonad.InstanceImpl{ .allocator = allocator };
    const NatStateFToState = NatTrans(StateFToStateNatImpl(cfg, StateS));
    const nat_statef_state = NatStateFToState.InstanceImpl{};

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = MonadFromImpl(ShowMonadImpl);
    const ArrayMonoid = Monoid(ArrayList(u8));
    const array_monoid = ArrayMonoid.InstanceImpl{ .allocator = allocator };
    const show_monad = ShowMonad.InstanceImpl{ .monoid_impl = array_monoid };
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.InstanceImpl{ .allocator = allocator };

    const ExistType = freetypes.GetExistentialType(F);
    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, StateS, u32));
    const PutF: FOpEnumInt = @intFromEnum(StateFCtorEnum.PutF);
    const buildPutF = StateFCtorDefs(cfg, StateS, u32).PutF.build;
    const GetF: FOpEnumInt = @intFromEnum(StateFCtorEnum.GetF);
    // The function operator build a FreeMonad(F, ExistType)
    const buildGetF = StateFCtorDefs(cfg, StateS, ExistType).GetF.build;
    const put_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
    };

    var free_state = try FreeMonad(cfg, F, u32).freeM(42, @constCast(put_ops));
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
        const Error = FreeMonad(cfg, F, ExistType).Error;
        fn get(s: u64) EffectVal(Error, ExistType) {
            return @intCast(s + 10);
        }
    }.get;

    const x_to_free_state = struct {
        const Error = FreeMonad(cfg, F, u32).Error;
        fn xToFreeState(x: ExistType) EffectVal(Error, FreeMonad(cfg, F, u32)) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37 + x)) },
            };
            const a = @as(u32, @intCast(x)) * 2;
            return FreeMonad(cfg, F, u32).freeM(a, @constCast(x_state_ops));
        }
    }.xToFreeState;

    var free_state1 = try FreeMonad(cfg, F, u32).freeFOp(x_to_free_state, GetF, try buildGetF(get_fn));
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
    free_state1 = try free_state1.appendFOp(state1_ops[0]);
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
    const cfg = getDefaultStateCfg(StateS, allocator);
    const F = StateF(cfg, StateS);
    const StateFFunctor = Functor(F);
    const statef_functor = StateFFunctor.InstanceImpl{ .allocator = allocator };
    const FStateMonad = Monad(freetypes.FreeM(cfg, F));
    var freem_monad = FStateMonad.InstanceImpl{
        .allocator = allocator,
        .funf_impl = statef_functor,
    };

    const StateMonad = Monad(StateContext(cfg).StateM(StateS));
    const state_monad = StateMonad.InstanceImpl{ .allocator = allocator };
    const NatStateFToState = NatTrans(StateFToStateNatImpl(cfg, StateS));
    const nat_statef_state = NatStateFToState.InstanceImpl{};

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = MonadFromImpl(ShowMonadImpl);
    const ArrayMonoid = Monoid(ArrayList(u8));
    const array_monoid = ArrayMonoid.InstanceImpl{ .allocator = allocator };
    const show_monad = ShowMonad.InstanceImpl{ .monoid_impl = array_monoid };
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.InstanceImpl{ .allocator = allocator };

    const ExistType = freetypes.GetExistentialType(F);
    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, StateS, u32));
    const PutF: FOpEnumInt = @intFromEnum(StateFCtorEnum.PutF);
    const buildPutF = StateFCtorDefs(cfg, StateS, u32).PutF.build;
    const GetF: FOpEnumInt = @intFromEnum(StateFCtorEnum.GetF);
    // The function operator build a FreeMonad(F, ExistType)
    const buildGetF = StateFCtorDefs(cfg, StateS, ExistType).GetF.build;
    const put_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
    };

    const get_fn = struct {
        const Error = FreeMonad(cfg, F, ExistType).Error;
        fn get(s: u64) EffectVal(Error, ExistType) {
            return @intCast(s + 10);
        }
    }.get;

    const x_to_free_state = struct {
        const Error = FreeMonad(cfg, F, u32).Error;
        fn xToFreeState(x: u64) EffectVal(Error, FreeMonad(cfg, F, u32)) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37 + x)) },
            };
            const a = @as(u32, @intCast(x)) * 2;
            return FreeMonad(cfg, F, u32).freeM(a, @constCast(x_state_ops));
        }
    }.xToFreeState;

    var free_state = try FreeMonad(cfg, F, u32).freeFOp(x_to_free_state, GetF, try buildGetF(get_fn));

    free_state = try free_state.appendFOps(put_ops);
    // When use InplaceMap mode to call fmap with free_state, do not deinit free_state.
    // defer free_state.deinit();
    const freem_mapped0 = try free_state.foldFree(nat_statef_state, statef_functor, state_monad);
    const res0_a, const res0_s = try freem_mapped0.runState(13);
    _ = freem_mapped0.strongUnref();
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
    const freem_mapped1 = try free_state1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res1_a, const res1_s = try freem_mapped1.runState(13);
    _ = freem_mapped1.strongUnref();
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
    const freem_mapped2 = try freem_monad.fmapLam(.InplaceMap, div_5_u32_lam, free_state1);
    defer freem_mapped2.deinit();
    const state2 = try freem_mapped2.foldFree(nat_statef_state, statef_functor, state_monad);
    const res2_a, const res2_s = try state2.runState(13);
    _ = state2.strongUnref();
    // ((37 + 10) * 2 + 3.14) / 5 = 19
    try testing.expectEqual(19, res2_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res2_s);
    const show_writer2 = try freem_mapped2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer2.deinit();
    // ((0 + 10) * 2 + 3.14) / 5 = 4
    try testing.expectEqual(4, show_writer2.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 23, PutF 37, GetF, PutF 47, ", show_writer2.w.items);
}

test "FreeMonad(StateF, A) fapply and fapplyLam" {
    const allocator = testing.allocator;
    const StateS = u64;
    const cfg = getDefaultStateCfg(StateS, allocator);
    const F = StateF(cfg, StateS);
    const StateFFunctor = Functor(F);
    const statef_functor = StateFFunctor.InstanceImpl{ .allocator = allocator };
    const FStateMonad = Monad(freetypes.FreeM(cfg, F));
    var freem_monad = FStateMonad.InstanceImpl{
        .allocator = allocator,
        .funf_impl = statef_functor,
    };

    const StateMonad = Monad(StateContext(cfg).StateM(StateS));
    const state_monad = StateMonad.InstanceImpl{ .allocator = allocator };
    const NatStateFToState = NatTrans(StateFToStateNatImpl(cfg, StateS));
    const nat_statef_state = NatStateFToState.InstanceImpl{};

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = MonadFromImpl(ShowMonadImpl);
    const ArrayMonoid = Monoid(ArrayList(u8));
    const array_monoid = ArrayMonoid.InstanceImpl{ .allocator = allocator };
    const show_monad = ShowMonad.InstanceImpl{ .monoid_impl = array_monoid };
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.InstanceImpl{ .allocator = allocator };

    const ExistType = freetypes.GetExistentialType(F);
    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, StateS, u32));
    const PutF: FOpEnumInt = @intFromEnum(StateFCtorEnum.PutF);
    const buildPutF = StateFCtorDefs(cfg, StateS, u32).PutF.build;
    const GetF: FOpEnumInt = @intFromEnum(StateFCtorEnum.GetF);
    // The function operator build a FreeMonad(F, ExistType)
    const buildGetF = StateFCtorDefs(cfg, StateS, ExistType).GetF.build;

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
    const pure_free_a1 = try pure_free_a.appendFOps(put_a_ops);
    defer pure_free_a1.deinit();
    const pure_free_af = try freem_monad.pure(&add_pi_f64);
    const pure_free_af1 = try pure_free_af.appendFOps(put_af_ops);
    defer pure_free_af1.deinit();
    const add_pi_f64_lam = testu.Add_x_f64_Lam{ ._x = 3.14 };
    const pure_free_flam = try freem_monad.pure(add_pi_f64_lam);
    const pure_free_flam1 = try pure_free_flam.appendFOps(put_flam_ops);
    defer pure_free_flam1.deinit();

    const pure_applied1 = try freem_monad.fapply(pure_free_af1, pure_free_a);
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

    const pure_applied2 = try freem_monad.fapply(pure_free_af1, pure_free_a1);
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

    const pure_applied3 = try freem_monad.fapplyLam(pure_free_flam1, pure_free_a1);
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
        const Error = FreeMonad(cfg, F, u32).Error;
        fn xToFreeState(x: u64) EffectVal(Error, FreeMonad(cfg, F, u32)) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37 + x)) },
            };
            const a = @as(u32, @intCast(x)) * 2;
            return FreeMonad(cfg, F, u32).freeM(a, @constCast(x_state_ops));
        }
    }.xToFreeState;

    const get_fn = struct {
        const Error = FreeMonad(cfg, F, ExistType).Error;
        fn get(s: u64) EffectVal(Error, ExistType) {
            return @intCast(s + 10);
        }
    }.get;

    var free_state = try FreeMonad(cfg, F, u32).freeFOp(x_to_free_state, GetF, try buildGetF(get_fn));
    defer free_state.deinit();
    const freem_applied1 = try freem_monad.fapply(pure_free_af1, free_state);
    defer freem_applied1.deinit();
    const state1 = try freem_applied1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res1_a, const res1_s = try state1.runState(13);
    _ = state1.strongUnref();
    // (17 + 10) * 2 + 3.14 = 57.14
    try testing.expectEqual(57.14, res1_a);
    // (17 + 10) + 37 = 64
    try testing.expectEqual(64, res1_s);
    const show_writer1 = try freem_applied1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer1.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer1.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, GetF, PutF 47, ", show_writer1.w.items);

    const freem_applied11 = try freem_monad.fapplyLam(pure_free_flam1, free_state);
    defer freem_applied11.deinit();
    const state11 = try freem_applied11.foldFree(nat_statef_state, statef_functor, state_monad);
    const res11_a, const res11_s = try state11.runState(13);
    _ = state11.strongUnref();
    // (17 + 10) * 2 + 3.14 = 57.14
    try testing.expectEqual(57.14, res11_a);
    // (17 + 10) + 37 = 64
    try testing.expectEqual(64, res11_s);
    const show_writer11 = try freem_applied11.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer11.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer11.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, GetF, PutF 47, ", show_writer11.w.items);

    const put_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
    };

    free_state = try free_state.appendFOps(put_ops);
    const freem_applied2 = try freem_monad.fapply(pure_free_af1, free_state);
    defer freem_applied2.deinit();
    const state2 = try freem_applied2.foldFree(nat_statef_state, statef_functor, state_monad);
    const res2_a, const res2_s = try state2.runState(13);
    _ = state2.strongUnref();
    // (37 + 10) * 2 + 3.14 = 97.14
    try testing.expectEqual(97.14, res2_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res2_s);
    const show_writer2 = try freem_applied2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer2.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer2.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, PutF 23, PutF 37, GetF, PutF 47, ", show_writer2.w.items);

    const freem_applied22 = try freem_monad.fapplyLam(pure_free_flam1, free_state);
    defer freem_applied22.deinit();
    const state22 = try freem_applied22.foldFree(nat_statef_state, statef_functor, state_monad);
    const res22_a, const res22_s = try state22.runState(13);
    _ = state22.strongUnref();
    // (37 + 10) * 2 + 3.14 = 97.14
    try testing.expectEqual(97.14, res22_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res22_s);
    const show_writer22 = try freem_applied22.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer22.deinit();
    // (0 + 10) * 2 + 3.14 = 23.14
    try testing.expectEqual(23.14, show_writer22.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, PutF 23, PutF 37, GetF, PutF 47, ", show_writer22.w.items);

    const FnType1 = *const fn (u32) f64;
    const x_to_free_state_fn = struct {
        const Error = FreeMonad(cfg, F, FnType1).Error;
        fn xToFreeState(x: u64) EffectVal(Error, FreeMonad(cfg, F, FnType1)) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(19 + x)) },
            };
            const res_fn = struct {
                fn f(a: u32) f64 {
                    return @as(f64, @floatFromInt(a)) + 6.18;
                }
            }.f;
            return FreeMonad(cfg, F, FnType1).freeM(&res_fn, @constCast(x_state_ops));
        }
    }.xToFreeState;

    var free_state_af1 = try FreeMonad(cfg, F, FnType1).freeFOp(x_to_free_state_fn, GetF, try buildGetF(get_fn));
    defer free_state_af1.deinit();
    const freem_applied3 = try freem_monad.fapply(free_state_af1, free_state);
    defer freem_applied3.deinit();
    const state3 = try freem_applied3.foldFree(nat_statef_state, statef_functor, state_monad);
    const res3_a, const res3_s = try state3.runState(13);
    _ = state3.strongUnref();
    // (37 + 10) * 2 + 6.18 = 100.18
    try testing.expectEqual(100.18, res3_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res3_s);
    const show_writer3 = try freem_applied3.foldFree(nat_statef_show, statef_functor, show_monad);
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
        const Error = FreeMonad(cfg, F, LamType1).Error;
        fn xToFreeState(x: u64) EffectVal(Error, FreeMonad(cfg, F, LamType1)) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(19 + x)) },
            };
            const res_lam = LamType1{ ._x = 6.18 };
            return FreeMonad(cfg, F, LamType1).freeM(res_lam, @constCast(x_state_ops));
        }
    }.xToFreeState;

    var free_state_lam1 = try FreeMonad(cfg, F, LamType1).freeFOp(x_to_free_state_lam, GetF, try buildGetF(get_fn));
    defer free_state_lam1.deinit();
    const freem_applied33 = try freem_monad.fapplyLam(free_state_lam1, free_state);
    defer freem_applied33.deinit();
    const state33 = try freem_applied33.foldFree(nat_statef_state, statef_functor, state_monad);
    const res33_a, const res33_s = try state33.runState(13);
    _ = state33.strongUnref();
    // (37 + 10) * 2 + 6.18 = 100.18
    try testing.expectEqual(100.18, res33_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res33_s);
    const show_writer33 = try freem_applied33.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer33.deinit();
    // (0 + 10) * 2 + 6.18 = 26.18
    try testing.expectEqual(26.18, show_writer33.a);
    // (0 + 10) + 37 = 47
    try testing.expectEqualSlices(u8, "GetF, PutF 29, PutF 23, PutF 37, GetF, PutF 47, ", show_writer33.w.items);

    const put_af1_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(33)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(21)) },
    };
    free_state_af1 = try free_state_af1.appendFOps(put_af1_ops);
    const freem_applied4 = try freem_monad.fapply(free_state_af1, free_state);
    defer freem_applied4.deinit();
    const state4 = try freem_applied4.foldFree(nat_statef_state, statef_functor, state_monad);
    const res4_a, const res4_s = try state4.runState(13);
    _ = state4.strongUnref();
    // (37 + 10) * 2 + 6.18 = 100.18
    try testing.expectEqual(100.18, res4_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res4_s);
    const show_writer4 = try freem_applied4.foldFree(nat_statef_show, statef_functor, show_monad);
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
    free_state_lam1 = try free_state_lam1.appendFOps(&put_flam1_ops);
    const freem_applied44 = try freem_monad.fapplyLam(free_state_lam1, free_state);
    defer freem_applied44.deinit();
    const state44 = try freem_applied44.foldFree(nat_statef_state, statef_functor, state_monad);
    const res44_a, const res44_s = try state44.runState(13);
    _ = state44.strongUnref();
    // (37 + 10) * 2 + 6.18 = 100.18
    try testing.expectEqual(100.18, res44_a);
    // (37 + 10) + 37 = 84
    try testing.expectEqual(84, res44_s);
    const show_writer44 = try freem_applied44.foldFree(nat_statef_show, statef_functor, show_monad);
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

test "FreeMonad(StateF, A) bind and join" {
    const allocator = testing.allocator;
    const StateS = u64;
    const cfg = getDefaultStateCfg(StateS, allocator);
    const F = StateF(cfg, StateS);
    const StateFFunctor = Functor(F);
    const statef_functor = StateFFunctor.InstanceImpl{ .allocator = allocator };
    const FStateMonad = Monad(freetypes.FreeM(cfg, F));
    var freem_monad = FStateMonad.InstanceImpl{
        .allocator = allocator,
        .funf_impl = statef_functor,
    };
    const FreeStateFImpl = @TypeOf(freem_monad);

    const StateMonad = Monad(StateContext(cfg).StateM(StateS));
    const state_monad = StateMonad.InstanceImpl{ .allocator = allocator };
    const NatStateFToState = NatTrans(StateFToStateNatImpl(cfg, StateS));
    const nat_statef_state = NatStateFToState.InstanceImpl{};

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = MonadFromImpl(ShowMonadImpl);
    const ArrayMonoid = Monoid(ArrayList(u8));
    const array_monoid = ArrayMonoid.InstanceImpl{ .allocator = allocator };
    const show_monad = ShowMonad.InstanceImpl{ .monoid_impl = array_monoid };
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.InstanceImpl{ .allocator = allocator };

    const ExistType = freetypes.GetExistentialType(F);
    const StateFCtorEnum = std.meta.DeclEnum(StateFCtorDefs(cfg, StateS, u32));
    const PutF: FOpEnumInt = @intFromEnum(StateFCtorEnum.PutF);
    const buildPutF = StateFCtorDefs(cfg, StateS, u32).PutF.build;
    const GetF: FOpEnumInt = @intFromEnum(StateFCtorEnum.GetF);
    // The function operator build a FreeMonad(F, ExistType)
    const buildGetF = StateFCtorDefs(cfg, StateS, ExistType).GetF.build;

    // test all variants of FreeMonad StateF A with pure value
    const put_a_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(25)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(19)) },
    };
    const put_b_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(17)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(35)) },
    };

    const pure_freem = try freem_monad.pure(@as(u32, 42));
    const pure_freem_a = try FreeMonad(cfg, F, u32).freeM(0, @constCast(put_a_ops));
    defer pure_freem_a.deinit();
    const pure_freem_b = try FreeMonad(cfg, F, u32).freeM(1, @constCast(put_b_ops));
    defer pure_freem_b.deinit();

    const k_u32 = struct {
        fn f(self: *const FreeStateFImpl, a: u32) !FreeMonad(cfg, F, f64) {
            const _a = if (a > 1) 0 else a;
            const ops_array = switch (_a) {
                0 => &[_]FOpInfo{},
                1 => &[_]FOpInfo{
                    .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37)) },
                    .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
                },
                else => @panic("The _a is not greater than 1"),
            };
            const b = @as(f64, @floatFromInt(a)) + 3.14;

            const freem = if (ops_array.len > 0)
                try FreeMonad(cfg, F, f64).freeM(b, @constCast(ops_array))
            else
                try self.pure(b);
            return freem;
        }
    }.f;

    const map_u32 = struct {
        fn f(a: u32) !FreeMonad(cfg, F, f64) {
            const _a = if (a > 1) 0 else a;
            const ops_array = switch (_a) {
                0 => &[_]FOpInfo{},
                1 => &[_]FOpInfo{
                    .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37)) },
                    .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
                },
                else => @panic("The _a is not greater than 1"),
            };
            const b = @as(f64, @floatFromInt(a)) + 3.14;

            const freem = if (ops_array.len > 0)
                try FreeMonad(cfg, F, f64).freeM(b, @constCast(ops_array))
            else
                FreeMonad(cfg, F, f64).pureM(b);
            return freem;
        }
    }.f;

    const pure_binded1 = try freem_monad.bind(u32, f64, pure_freem, k_u32);
    defer pure_binded1.deinit();
    const pure_state1 = try pure_binded1.foldFree(nat_statef_state, statef_functor, state_monad);
    const pure_res1_a, const pure_res1_s = try pure_state1.runState(13);
    _ = pure_state1.strongUnref();
    try testing.expectEqual(45.14, pure_res1_a);
    try testing.expectEqual(13, pure_res1_s);
    const show_pure1 = try pure_binded1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_pure1.deinit();
    try testing.expectEqual(45.14, show_pure1.a);
    try testing.expectEqualSlices(u8, "", show_pure1.w.items);

    const pure_binded2 = try freem_monad.bind(u32, f64, pure_freem_a, k_u32);
    defer pure_binded2.deinit();
    const pure_state2 = try pure_binded2.foldFree(nat_statef_state, statef_functor, state_monad);
    const pure_res2_a, const pure_res2_s = try pure_state2.runState(13);
    _ = pure_state2.strongUnref();
    try testing.expectEqual(3.14, pure_res2_a);
    try testing.expectEqual(25, pure_res2_s);
    const show_pure2 = try pure_binded2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_pure2.deinit();
    try testing.expectEqual(3.14, show_pure2.a);
    try testing.expectEqualSlices(u8, "PutF 19, PutF 25, ", show_pure2.w.items);

    const pure_mma2 = try freem_monad.fmap(.NewValMap, map_u32, pure_freem_a);
    defer pure_mma2.deinit();
    const pure_joined2 = try freem_monad.join(f64, pure_mma2);
    defer pure_joined2.deinit();
    const pure_state22 = try pure_joined2.foldFree(nat_statef_state, statef_functor, state_monad);
    const pure_res22_a, const pure_res22_s = try pure_state22.runState(13);
    _ = pure_state22.strongUnref();
    try testing.expectEqual(3.14, pure_res22_a);
    try testing.expectEqual(25, pure_res22_s);
    const show_pure22 = try pure_joined2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_pure22.deinit();
    try testing.expectEqual(3.14, show_pure22.a);
    try testing.expectEqualSlices(u8, "PutF 19, PutF 25, ", show_pure22.w.items);

    const pure_binded3 = try freem_monad.bind(u32, f64, pure_freem_b, k_u32);
    defer pure_binded3.deinit();
    const pure_state3 = try pure_binded3.foldFree(nat_statef_state, statef_functor, state_monad);
    const pure_res3_a, const pure_res3_s = try pure_state3.runState(13);
    _ = pure_state3.strongUnref();
    try testing.expectApproxEqRel(4.14, pure_res3_a, std.math.floatEps(f64));
    try testing.expectEqual(37, pure_res3_s);
    const show_pure3 = try pure_binded3.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_pure3.deinit();
    try testing.expectApproxEqRel(4.14, show_pure3.a.?, std.math.floatEps(f64));
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, PutF 23, PutF 37, ", show_pure3.w.items);

    const pure_mma3 = try freem_monad.fmap(.NewValMap, map_u32, pure_freem_b);
    defer pure_mma3.deinit();
    const pure_joined3 = try freem_monad.join(f64, pure_mma3);
    defer pure_joined3.deinit();
    const pure_state33 = try pure_joined3.foldFree(nat_statef_state, statef_functor, state_monad);
    const pure_res33_a, const pure_res33_s = try pure_state33.runState(13);
    _ = pure_state33.strongUnref();
    try testing.expectApproxEqRel(4.14, pure_res33_a, std.math.floatEps(f64));
    try testing.expectEqual(37, pure_res33_s);
    const show_pure33 = try pure_joined3.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_pure33.deinit();
    try testing.expectApproxEqRel(4.14, show_pure33.a.?, std.math.floatEps(f64));
    try testing.expectEqualSlices(u8, "PutF 35, PutF 17, PutF 23, PutF 37, ", show_pure33.w.items);

    // test all variants of FreeMonad(StateF, A) with GetF operator
    const x_to_free_state_even = struct {
        const Error = FreeMonad(cfg, F, u32).Error;
        fn xToFreeState(x: u64) EffectVal(Error, FreeMonad(cfg, F, u32)) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37 + x)) },
            };
            // std.debug.print("x_to_free_state_even, x={d}\n", .{x});
            const a = @as(u32, @intCast(x)) * 2;
            return FreeMonad(cfg, F, u32).freeM(a, @constCast(x_state_ops));
        }
    }.xToFreeState;

    const x_to_free_state_odd = struct {
        const Error = FreeMonad(cfg, F, u32).Error;
        fn xToFreeState(x: u64) EffectVal(Error, FreeMonad(cfg, F, u32)) {
            const x_state_ops = &[_]FOpInfo{
                .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(37 + x)) },
            };
            // std.debug.print("x_to_free_state_odd, x={d}\n", .{x});
            const a = @as(u32, @intCast(x)) * 3;
            return FreeMonad(cfg, F, u32).freeM(a, @constCast(x_state_ops));
        }
    }.xToFreeState;

    const get_fn = struct {
        const Error = FreeMonad(cfg, F, ExistType).Error;
        fn get(s: u64) EffectVal(Error, ExistType) {
            return @intCast(s + 7);
        }
    }.get;

    const getf_k_u32 = struct {
        fn f(self: *const FreeStateFImpl, a: u32) !FreeMonad(cfg, F, f64) {
            _ = self;
            const is_even = if (a & 0x1 == 1) false else true;
            const ops_array = switch (is_even) {
                true => &[_]FOpInfo{},
                false => &[_]FOpInfo{
                    .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(41)) },
                    .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
                },
            };

            const k_x_to_freem = struct {
                const Error = FreeMonad(cfg, F, f64).Error;
                fn xToFreeState(x: u64) EffectVal(Error, FreeMonad(cfg, F, f64)) {
                    const x_state_ops = &[_]FOpInfo{
                        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(19 + x)) },
                    };
                    // std.debug.print("k_x_to_freem, x={d}\n", .{x});
                    const k_a = @as(f64, @floatFromInt(x)) + 6.18;
                    return FreeMonad(cfg, F, f64).freeM(k_a, @constCast(x_state_ops));
                }
            }.xToFreeState;

            const k_get_fn = struct {
                const Error = FreeMonad(cfg, F, ExistType).Error;
                fn get(s: u64) EffectVal(Error, ExistType) {
                    // std.debug.print("k_get_fn, s={d}\n", .{s});
                    return @intCast(s + 29);
                }
            }.get;

            var freem = try FreeMonad(cfg, F, f64).freeFOp(k_x_to_freem, GetF, try buildGetF(k_get_fn));
            if (ops_array.len > 0)
                freem = try freem.appendFOps(ops_array);
            return freem;
        }
    }.f;

    const getf_map_u32 = struct {
        fn f(a: u32) !FreeMonad(cfg, F, f64) {
            const is_even = if (a & 0x1 == 1) false else true;
            const ops_array = switch (is_even) {
                true => &[_]FOpInfo{},
                false => &[_]FOpInfo{
                    .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(41)) },
                    .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(23)) },
                },
            };

            const map_x_to_freem = struct {
                const Error = FreeMonad(cfg, F, f64).Error;
                fn xToFreeState(x: u64) EffectVal(Error, FreeMonad(cfg, F, f64)) {
                    const x_state_ops = &[_]FOpInfo{
                        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(19 + x)) },
                    };
                    const k_a = @as(f64, @floatFromInt(x)) + 6.18;
                    return FreeMonad(cfg, F, f64).freeM(k_a, @constCast(x_state_ops));
                }
            }.xToFreeState;

            const map_get_fn = struct {
                const Error = FreeMonad(cfg, F, ExistType).Error;
                fn get(s: u64) EffectVal(Error, ExistType) {
                    return @intCast(s + 29);
                }
            }.get;

            var freem = try FreeMonad(cfg, F, f64).freeFOp(map_x_to_freem, GetF, try buildGetF(map_get_fn));
            if (ops_array.len > 0)
                freem = try freem.appendFOps(ops_array);
            return freem;
        }
    }.f;

    var free_state = try FreeMonad(cfg, F, u32).freeFOp(x_to_free_state_even, GetF, try buildGetF(get_fn));
    defer free_state.deinit();
    const free_binded1 = try freem_monad.bind(u32, f64, free_state, getf_k_u32);
    defer free_binded1.deinit();
    const state1 = try free_binded1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res1_a, const res1_s = try state1.runState(13);
    _ = state1.strongUnref();
    // (13 + 7) + 37 + 29 + 6.18 = 92.18
    try testing.expectEqual(92.18, res1_a);
    // (13 + 7) + 37 + 29 + 19 = 105
    try testing.expectEqual(105, res1_s);
    const show_writer1 = try free_binded1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer1.deinit();
    // (0 + 29) + 6.18 = 35.18
    try testing.expectEqual(35.18, show_writer1.a);
    // (0 + 7) + 37 = 44
    // (0 + 29) + 19 = 48
    try testing.expectEqualSlices(u8, "GetF, PutF 44, GetF, PutF 48, ", show_writer1.w.items);

    const free_mma1 = try freem_monad.fmap(.NewValMap, getf_map_u32, free_state);
    defer free_mma1.deinit();
    const free_joined1 = try freem_monad.join(f64, free_mma1);
    defer free_joined1.deinit();
    const state11 = try free_joined1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res11_a, const res11_s = try state11.runState(13);
    _ = state11.strongUnref();
    // (13 + 7) + 37 + 29 + 6.18 = 92.18
    try testing.expectEqual(92.18, res11_a);
    // (13 + 7) + 37 + 29 + 19 = 105
    try testing.expectEqual(105, res11_s);
    const show_writer11 = try free_joined1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer11.deinit();
    // (0 + 29) + 6.18 = 35.18
    try testing.expectEqual(35.18, show_writer11.a);
    // (0 + 7) + 37 = 44
    // (0 + 29) + 19 = 48
    try testing.expectEqualSlices(u8, "GetF, PutF 44, GetF, PutF 48, ", show_writer11.w.items);

    const put_mma_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(17)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(35)) },
    };

    free_state = try free_state.appendFOps(put_mma_ops);
    const free_binded2 = try freem_monad.bind(u32, f64, free_state, getf_k_u32);
    defer free_binded2.deinit();
    const state2 = try free_binded2.foldFree(nat_statef_state, statef_functor, state_monad);
    const res2_a, const res2_s = try state2.runState(13);
    _ = state2.strongUnref();
    // (17 + 7) + 37 + 29 + 6.18 = 96.18
    try testing.expectEqual(96.18, res2_a);
    // (17 + 7) + 37 + 29 + 19 = 109
    try testing.expectEqual(109, res2_s);
    const show_writer2 = try free_binded2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer2.deinit();
    // (0 + 29) + 6.18 = 35.18
    try testing.expectEqual(35.18, show_writer2.a);
    // (0 + 7) + 37 = 44
    // (0 + 29) + 19 = 48
    try testing.expectEqualSlices(
        u8,
        "PutF 35, PutF 17, GetF, PutF 44, GetF, PutF 48, ",
        show_writer2.w.items,
    );

    const free_mma2 = try freem_monad.fmap(.NewValMap, getf_map_u32, free_state);
    defer free_mma2.deinit();
    const free_joined2 = try freem_monad.join(f64, free_mma2);
    defer free_joined2.deinit();
    const state22 = try free_joined2.foldFree(nat_statef_state, statef_functor, state_monad);
    const res22_a, const res22_s = try state22.runState(13);
    _ = state22.strongUnref();
    // (17 + 7) + 37 + 29 + 6.18 = 96.18
    try testing.expectEqual(96.18, res22_a);
    // (17 + 7) + 37 + 29 + 19 = 109
    try testing.expectEqual(109, res22_s);
    const show_writer22 = try free_joined2.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer22.deinit();
    // (0 + 29) + 6.18 = 35.18
    try testing.expectEqual(35.18, show_writer22.a);
    // (0 + 7) + 37 = 44
    // (0 + 29) + 19 = 48
    try testing.expectEqualSlices(
        u8,
        "PutF 35, PutF 17, GetF, PutF 44, GetF, PutF 48, ",
        show_writer22.w.items,
    );

    var free_state_odd = try FreeMonad(cfg, F, u32).freeFOp(x_to_free_state_odd, GetF, try buildGetF(get_fn));
    defer free_state_odd.deinit();
    const free_binded3 = try freem_monad.bind(u32, f64, free_state_odd, getf_k_u32);
    defer free_binded3.deinit();
    const state3 = try free_binded3.foldFree(nat_statef_state, statef_functor, state_monad);
    const res3_a, const res3_s = try state3.runState(12);
    _ = state3.strongUnref();
    // (41 + 29) + 6.18 = 76.18
    try testing.expectEqual(76.18, res3_a);
    // (41 + 29) + 19 = 89
    try testing.expectEqual(89, res3_s);
    const show_writer3 = try free_binded3.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer3.deinit();
    // (0 + 29) + 6.18 = 35.18
    try testing.expectEqual(35.18, show_writer3.a);
    // (0 + 7) + 37 = 44
    // (0 + 29) + 19 = 48
    try testing.expectEqualSlices(
        u8,
        "GetF, PutF 44, PutF 23, PutF 41, GetF, PutF 48, ",
        show_writer3.w.items,
    );

    const free_mma3 = try freem_monad.fmap(.NewValMap, getf_map_u32, free_state_odd);
    defer free_mma3.deinit();
    const free_joined3 = try freem_monad.join(f64, free_mma3);
    defer free_joined3.deinit();
    const state33 = try free_joined3.foldFree(nat_statef_state, statef_functor, state_monad);
    const res33_a, const res33_s = try state33.runState(12);
    _ = state33.strongUnref();
    // (41 + 29) + 6.18 = 76.18
    try testing.expectEqual(76.18, res33_a);
    // (41 + 29) + 19 = 89
    try testing.expectEqual(89, res33_s);
    const show_writer33 = try free_joined3.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer33.deinit();
    // (0 + 29) + 6.18 = 35.18
    try testing.expectEqual(35.18, show_writer33.a);
    // (0 + 7) + 37 = 44
    // (0 + 29) + 19 = 48
    try testing.expectEqualSlices(
        u8,
        "GetF, PutF 44, PutF 23, PutF 41, GetF, PutF 48, ",
        show_writer33.w.items,
    );

    const put_mma2_ops = &[_]FOpInfo{
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(17)) },
        .{ .op_e = PutF, .op_lam = @bitCast(try buildPutF(35)) },
    };

    free_state_odd = try free_state_odd.appendFOps(put_mma2_ops);
    const free_binded4 = try freem_monad.bind(u32, f64, free_state_odd, getf_k_u32);
    defer free_binded4.deinit();
    const state4 = try free_binded4.foldFree(nat_statef_state, statef_functor, state_monad);
    const res4_a, const res4_s = try state4.runState(12);
    _ = state4.strongUnref();
    // (17 + 7) + 37 + 29 + 6.18 = 96.18
    try testing.expectEqual(96.18, res4_a);
    // (17 + 7) + 37 + 29 + 19 = 109
    try testing.expectEqual(109, res4_s);
    const show_writer4 = try free_binded4.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer4.deinit();
    // (0 + 29) + 6.18 = 35.18
    try testing.expectEqual(35.18, show_writer4.a);
    // (0 + 7) + 37 = 44
    // (0 + 29) + 19 = 48
    try testing.expectEqualSlices(
        u8,
        "PutF 35, PutF 17, GetF, PutF 44, PutF 23, PutF 41, GetF, PutF 48, ",
        show_writer4.w.items,
    );

    const free_mma4 = try freem_monad.fmap(.NewValMap, getf_map_u32, free_state_odd);
    defer free_mma4.deinit();
    const free_joined4 = try freem_monad.join(f64, free_mma4);
    defer free_joined4.deinit();
    const state44 = try free_joined4.foldFree(nat_statef_state, statef_functor, state_monad);
    const res44_a, const res44_s = try state44.runState(12);
    _ = state44.strongUnref();
    // (17 + 7) + 37 + 29 + 6.18 = 96.18
    try testing.expectEqual(96.18, res44_a);
    // (17 + 7) + 37 + 29 + 19 = 109
    try testing.expectEqual(109, res44_s);
    const show_writer44 = try free_joined4.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer44.deinit();
    // (0 + 29) + 6.18 = 35.18
    try testing.expectEqual(35.18, show_writer4.a);
    // (0 + 7) + 37 = 44
    // (0 + 29) + 19 = 48
    try testing.expectEqualSlices(
        u8,
        "PutF 35, PutF 17, GetF, PutF 44, PutF 23, PutF 41, GetF, PutF 48, ",
        show_writer44.w.items,
    );
}

test "runDo FreeMonad(StateF, A) " {
    const input1: u32 = 42;

    const allocator = testing.allocator;
    const StateS = u32;
    const cfg = getDefaultStateCfg(StateS, allocator);
    const CfgError = cfg.errors;
    const F = StateF(cfg, StateS);
    const StateFFunctor = Functor(F);
    const statef_functor = StateFFunctor.InstanceImpl{ .allocator = allocator };
    const FStateMonad = Monad(freetypes.FreeM(cfg, F));
    const freem_monad = FStateMonad.InstanceImpl{
        .allocator = allocator,
        .funf_impl = statef_functor,
    };
    const FreeStateFImpl = @TypeOf(freem_monad);

    const StateMonad = Monad(StateContext(cfg).StateM(StateS));
    const state_monad = StateMonad.InstanceImpl{ .allocator = allocator };
    const NatStateFToState = NatTrans(StateFToStateNatImpl(cfg, StateS));
    const nat_statef_state = NatStateFToState.InstanceImpl{};

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = MonadFromImpl(ShowMonadImpl);
    const ArrayMonoid = Monoid(ArrayList(u8));
    const array_monoid = ArrayMonoid.InstanceImpl{ .allocator = allocator };
    const show_monad = ShowMonad.InstanceImpl{ .monoid_impl = array_monoid };
    const NatStateFToShow = NatTrans(StateFShowNatImpl(cfg, StateS));
    const nat_statef_show = NatStateFToShow.InstanceImpl{ .allocator = allocator };

    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: FreeStateFImpl,
        param1: u32,

        // intermediate variable
        b: u32 = undefined,

        const Ctx = @This();
        pub const Error: ?type = FreeStateFImpl.Error;

        fn deinit(ctx: Ctx) void {
            _ = ctx;
        }

        // the do context struct must has startDo function
        pub fn startDo(impl: *FreeStateFImpl) FreeStateFImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            const s: StateS = 17;
            // PutF(s, ctx.param1)
            return liftPutF(cfg, s, ctx.param1);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *FreeStateFImpl, a: u32) FreeStateFImpl.MbType(f64) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            ctx.b = a;
            const add_x_f64 = struct {
                _x: f64,
                const Self = @This();
                pub fn call(self: *const Self, in: u32) EffectVal(CfgError, f64) {
                    return @as(f64, @floatFromInt(in)) + self._x;
                }
            }{ ._x = @floatFromInt(a) };
            // GetF (\s -> s + a)
            return liftGetF(cfg, add_x_f64);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *FreeStateFImpl, a: f64) FreeStateFImpl.MbType(u32) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            const div_x_u32 = testu.Div_x_u32_Lam{ ._x = 7 };
            const n = div_x_u32.call(a);
            return liftPutF(cfg, ctx.b, n + ctx.b);
        }
    }{ .monad_impl = freem_monad, .param1 = input1 };
    defer do_ctx.deinit();
    var free_state1 = try runDo(&do_ctx);
    defer free_state1.deinit();

    const state1 = try free_state1.foldFree(nat_statef_state, statef_functor, state_monad);
    const res1_a, const res1_s = try state1.runState(12);
    _ = state1.strongUnref();
    // (42 + 17) / 7 + 42 = 50
    try testing.expectEqual(50, res1_a);
    // s = ctx.b = ctx.param1 = 42
    try testing.expectEqual(42, res1_s);
    const show_writer1 = try free_state1.foldFree(nat_statef_show, statef_functor, show_monad);
    defer show_writer1.deinit();
    // (42 + 0) / 7 + 42 = 48
    try testing.expectEqual(48, show_writer1.a);
    // s = ctx.b = ctx.param1 = 42
    try testing.expectEqualSlices(u8, "PutF 17, GetF, PutF 42, ", show_writer1.w.items);
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

        pub const Error: ?type = Allocator.Error;

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
            self: *const Self,
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

        pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
            const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
            _ = _A;
            const _a = if (has_err) try a else a;
            return .{ .a = _a, .w = try self.monoid_impl.mempty() };
        }

        pub fn fapply(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            // ff: F(*const fn (A) B),
            ff: anytype,
            fa: F(ApplyFnInType(Self, @TypeOf(ff))),
        ) AFbType(ApplyFnRetType(Self, @TypeOf(ff))) {
            const B = ApplyFnRetType(Self, @TypeOf(ff));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;
            const f = ff.a;
            const _b = if (has_err) try f(fa.a) else f(fa.a);
            return .{ .a = _b, .w = try self.monoid_impl.mappend(ff.w, fa.w) };
        }

        pub fn fapplyLam(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(ApplyLamInType(Self, @TypeOf(flam))),
        ) AFbType(ApplyLamRetType(Self, @TypeOf(flam))) {
            const B = ApplyLamRetType(Self, @TypeOf(flam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;
            const lam = flam.a;
            const _b = if (has_err) try lam.call(fa.a) else lam.call(fa.a);
            return .{ .a = _b, .w = try self.monoid_impl.mappend(flam.w, fa.w) };
        }

        pub fn bind(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*const Self, A) MbType(B),
        ) MbType(B) {
            const mb = try k(ma.a);
            return .{ .a = mb.a, .w = try self.monoid_impl.mappend(ma.w, mb.w) };
        }

        pub fn join(
            self: *const Self,
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
    const WriterMonoid = Monoid(W);
    const WriterMonoidImpl = WriterMonoid.InstanceImpl;
    return struct {
        fn MWriterMaybeF(comptime A: type) type {
            return struct {
                a: Maybe(A),
                w: W,

                const Self = @This();
                pub const BaseType = A;

                pub const FunctorImpl = MWriterMaybeMonadImpl(WriterMonoidImpl, W);
                pub const ApplicativeImpl = FunctorImpl;
                pub const MonadImpl = FunctorImpl;

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

        pub const Error: ?type = Allocator.Error;

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
            self: *const Self,
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

        pub fn pure(self: *const Self, a: anytype) APaType(@TypeOf(a)) {
            const has_err, const _A = comptime isErrorUnionOrVal(@TypeOf(a));
            _ = _A;
            const _a = if (has_err) try a else a;
            return .{ .a = _a, .w = try self.monoid_impl.mempty() };
        }

        pub fn fapply(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            // ff: F(*const fn (A) B),
            ff: anytype,
            fa: F(ApplyFnInType(Self, @TypeOf(ff))),
        ) AFbType(ApplyFnRetType(Self, @TypeOf(ff))) {
            const B = ApplyFnRetType(Self, @TypeOf(ff));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;
            const f = ff.a;
            const _b = if (fa.a) |_a| blk_t: {
                break :blk_t if (has_err) try f(_a) else f(_a);
            } else null;
            return .{ .a = _b, .w = try self.monoid_impl.mappend(ff.w, fa.w) };
        }

        pub fn fapplyLam(
            self: *const Self,
            // applicative function: F (a -> b), fa: F a
            flam: anytype, // a F(lambda) that present F(*const fn (A) B),
            fa: F(ApplyLamInType(Self, @TypeOf(flam))),
        ) AFbType(ApplyLamRetType(Self, @TypeOf(flam))) {
            const B = ApplyLamRetType(Self, @TypeOf(flam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);
            _ = _B;
            const lam = flam.a;
            const _b = if (fa.a) |_a| blk_t: {
                break :blk_t if (has_err) try lam.call(_a) else lam.call(_a);
            } else null;
            return .{ .a = _b, .w = try self.monoid_impl.mappend(flam.w, fa.w) };
        }
        pub fn bind(
            self: *const Self,
            comptime A: type,
            comptime B: type,
            // monad function: (a -> M b), ma: M a
            ma: F(A),
            k: *const fn (*const Self, A) MbType(B),
        ) MbType(B) {
            const mb = if (ma.a) |_a|
                try k(self, _a)
            else
                .{ .a = null, .w = self.monoid_impl.mempty() };
            return .{ .a = mb.a, .w = try self.monoid_impl.mappend(ma.w, mb.w) };
        }

        pub fn join(
            self: *const Self,
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

const std = @import("std");
const zcats = @import("zcats");

const testing = std.testing;
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;
const ArrayList = std.ArrayList;

const TCtor = zcats.TCtor;

const MapFnInType = zcats.MapFnInType;
const MapFnRetType = zcats.MapFnRetType;
const MapLamInType = zcats.MapLamInType;
const MapLamRetType = zcats.MapLamRetType;

const FMapMode = zcats.FMapMode;
const MapFnKind = zcats.MapFnKind;
const isMapRef = zcats.isMapRef;
const isInplaceMap = zcats.isInplaceMap;
const isErrorUnionOrVal = zcats.isErrorUnionOrVal;

const Functor = zcats.Functor;
const NatTrans = zcats.NatTrans;
const Applicative = zcats.Applicative;
const Monad = zcats.Monad;
const ArrayListMonadImpl = zcats.ArrayListMonadImpl;

const FunctorFxTypes = zcats.FunctorFxTypes;
const ApplicativeFxTypes = zcats.ApplicativeFxTypes;
const MonadFxTypes = zcats.MonadFxTypes;
const runDo = zcats.runDo;
const FOpInfo = zcats.FOpInfo;
const FOpEnumInt = zcats.FOpEnumInt;

const ArrayListMonoidImpl = zcats.ArrayListMonoidImpl;
const FreeMonad = zcats.FreeMonad;
const FreeMonadImpl = zcats.FreeMonadImpl;

pub fn freeMonadSmaple() !void {
    try runStackCalcSample();
}

const Int = i64;

// The Kont is a continuation type
fn StackCalcF(Kont: type) type {
    return union(enum) {
        push: struct { Int, Kont },
        pop: Kont,
        add: Kont,
        mul: Kont,

        const Self = @This();
        pub const BaseType = Kont;
        pub const Error = error{};
        pub const ExistentialType = Int;
        pub const OpCtorDefs = GetOpCtorDefs();

        fn GetOpCtorDefs() type {
            const op_ctor_defs = StackCalcFCtorDefs(Kont);
            const CtorEnum = std.meta.DeclEnum(op_ctor_defs);
            const push_e = @intFromEnum(std.meta.activeTag(Self{ .push = undefined }));
            const pop_e = @intFromEnum(std.meta.activeTag(Self{ .pop = undefined }));
            const add_e = @intFromEnum(std.meta.activeTag(Self{ .add = undefined }));
            const mul_e = @intFromEnum(std.meta.activeTag(Self{ .mul = undefined }));
            // Check if it has same order of {Push, Pop, Add, Mul}
            assert(@intFromEnum(CtorEnum.Push) == push_e);
            assert(@intFromEnum(CtorEnum.Pop) == pop_e);
            assert(@intFromEnum(CtorEnum.Add) == add_e);
            assert(@intFromEnum(CtorEnum.Mul) == mul_e);
            return op_ctor_defs;
        }

        pub fn deinit(self: Self) void {
            _ = self;
        }
    };
}

const StackCalcFunctorImpl = struct {
    none: void = {},

    const Self = @This();

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = StackCalcF;

    /// Get base type of F(A), it is must just is A.
    pub fn BaseType(comptime State: type) type {
        return std.meta.Child(State).StateA;
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
        fa: anytype, // StateF(cfg, S, A)
        comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
    ) void {
        _ = free_fn;
        fa.deinit();
    }

    pub fn fmap(
        self: *Self,
        comptime K: MapFnKind,
        map_fn: anytype,
        fa: FaType(K, @TypeOf(map_fn)),
    ) FbType(@TypeOf(map_fn)) {
        _ = self;
        // const A = MapFnInType(@TypeOf(map_fn));
        const B = MapFnRetType(@TypeOf(map_fn));
        const has_err, const _B = comptime isErrorUnionOrVal(B);
        _ = _B;
        const _fa = if (comptime isMapRef(K)) fa.* else fa;

        switch (_fa) {
            .push => {
                const b = if (comptime isMapRef(K))
                    map_fn(&fa.push[1])
                else
                    map_fn(fa.push[1]);
                const _b = if (has_err) try b else b;
                return .{ .push = .{ fa.push[0], _b } };
            },
            .pop => {
                const b = if (comptime isMapRef(K))
                    map_fn(&fa.pop)
                else
                    map_fn(fa.pop);
                const _b = if (has_err) try b else b;
                return .{ .pop = _b };
            },
            .add => {
                const b = if (comptime isMapRef(K))
                    map_fn(&fa.add)
                else
                    map_fn(fa.add);
                const _b = if (has_err) try b else b;
                return .{ .add = _b };
            },
            .mul => {
                const b = if (comptime isMapRef(K))
                    map_fn(&fa.mul)
                else
                    map_fn(fa.mul);
                const _b = if (has_err) try b else b;
                return .{ .mul = _b };
            },
        }
    }

    pub fn fmapLam(
        self: *const Self,
        comptime K: MapFnKind,
        map_lam: anytype,
        fa: FaLamType(K, @TypeOf(map_lam)),
    ) FbLamType(@TypeOf(map_lam)) {
        _ = self;
        // const A = MapLamInType(@TypeOf(map_lam));
        const B = MapLamRetType(@TypeOf(map_lam));
        const has_err, const _B = comptime isErrorUnionOrVal(B);
        _ = _B;
        const _fa = if (comptime isMapRef(K)) fa.* else fa;

        switch (_fa) {
            .push => {
                const b = if (comptime isMapRef(K))
                    map_lam.call(&fa.push[1])
                else
                    map_lam.call(fa.push[1]);
                const _b = if (has_err) try b else b;
                return .{ .push = .{ fa.push[0], _b } };
            },
            .pop => {
                const b = if (comptime isMapRef(K))
                    map_lam.call(&fa.pop)
                else
                    map_lam.call(fa.pop);
                const _b = if (has_err) try b else b;
                return .{ .pop = _b };
            },
            .add => {
                const b = if (comptime isMapRef(K))
                    map_lam.call(&fa.add)
                else
                    map_lam.call(fa.add);
                const _b = if (has_err) try b else b;
                return .{ .add = _b };
            },
            .mul => {
                const b = if (comptime isMapRef(K))
                    map_lam.call(&fa.mul)
                else
                    map_lam.call(fa.mul);
                const _b = if (has_err) try b else b;
                return .{ .mul = _b };
            },
        }
    }
};

/// All value constructors for StackCalcF Functor
fn StackCalcFCtorDefs(comptime A: type) type {
    const Error = Allocator.Error;

    // Define Op constructor lambdas for StateF
    return struct {
        // The order of PutF and GetF must be same as order of putf and getf in StateF
        pub const Push = PushLam;
        pub const Pop = PopLam;
        pub const Add = AddLam;
        pub const Mul = MulLam;

        const SelfCtor = @This();
        const CtorEnum = std.meta.DeclEnum(SelfCtor);
        const Push_E: FOpEnumInt = @intFromEnum(CtorEnum.Push);
        const Pop_E: FOpEnumInt = @intFromEnum(CtorEnum.Pop);
        const Add_E: FOpEnumInt = @intFromEnum(CtorEnum.Add);
        const Mul_E: FOpEnumInt = @intFromEnum(CtorEnum.Mul);

        const PushLam = extern struct {
            lam_ctx: Int = 0,
            const Self = @This();
            pub fn build(n: Int) Error!Self {
                return .{ .lam_ctx = n };
            }

            pub fn fpureToFreem(FreeMType: type, fpure: StackCalcF(A)) Error!FreeMType {
                const ops_array = [_]FOpInfo{
                    .{ .op_e = Push_E, .op_lam = @bitCast(try build(fpure.push[0])) },
                };
                const a = fpure.push[1];
                return FreeMType.freeM(a, @constCast(&ops_array));
            }

            pub fn deinit(self: Self) void {
                _ = self;
            }

            pub fn call(self: *Self, a: A) StackCalcF(A) {
                return .{ .push = .{ self.lam_ctx, a } };
            }
        };

        const PopLam = extern struct {
            lam_ctx: u64 = 0,
            const Self = @This();
            pub fn build() Error!Self {
                return .{};
            }

            pub fn fpureToFreem(FreeMType: type, fpure: StackCalcF(A)) Error!FreeMType {
                const ops_array = [_]FOpInfo{
                    .{ .op_e = Pop_E, .op_lam = @bitCast(try build()) },
                };
                const a = fpure.pop;
                return FreeMType.freeM(a, @constCast(&ops_array));
            }

            pub fn deinit(self: Self) void {
                _ = self;
            }

            pub fn call(self: *Self, a: A) StackCalcF(A) {
                _ = self;
                return .{ .pop = a };
            }
        };

        const AddLam = extern struct {
            lam_ctx: u64 = 0,
            const Self = @This();
            pub fn build() Error!Self {
                return .{};
            }

            pub fn fpureToFreem(FreeMType: type, fpure: StackCalcF(A)) Error!FreeMType {
                const ops_array = [_]FOpInfo{
                    .{ .op_e = Add_E, .op_lam = @bitCast(try build()) },
                };
                const a = fpure.add;
                return FreeMType.freeM(a, @constCast(&ops_array));
            }

            pub fn deinit(self: Self) void {
                _ = self;
            }

            pub fn call(self: *Self, a: A) StackCalcF(A) {
                _ = self;
                return .{ .add = a };
            }
        };

        const MulLam = extern struct {
            lam_ctx: u64 = 0,
            const Self = @This();
            pub fn build() Error!Self {
                return .{};
            }

            pub fn fpureToFreem(FreeMType: type, fpure: StackCalcF(A)) Error!FreeMType {
                const ops_array = [_]FOpInfo{
                    .{ .op_e = Mul_E, .op_lam = @bitCast(try build()) },
                };
                const a = fpure.mul;
                return FreeMType.freeM(a, @constCast(&ops_array));
            }

            pub fn deinit(self: Self) void {
                _ = self;
            }

            pub fn call(self: *Self, a: A) StackCalcF(A) {
                _ = self;
                return .{ .mul = a };
            }
        };
    };
}

fn liftPush(comptime cfg: anytype, n: Int) !FreeMonad(cfg, StackCalcF, void) {
    const A = void;
    const F = StackCalcF;

    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(A));
    const Push: FOpEnumInt = @intFromEnum(CtorEnum.Push);
    const buildPush = StackCalcFCtorDefs(A).Push.build;
    const push_ops = &[_]FOpInfo{
        .{ .op_e = Push, .op_lam = @bitCast(try buildPush(n)) },
    };
    return FreeMonad(cfg, F, void).freeM({}, @constCast(push_ops));
}

fn liftPop(comptime cfg: anytype) !FreeMonad(cfg, StackCalcF, void) {
    const A = void;
    const F = StackCalcF;

    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(A));
    const Pop: FOpEnumInt = @intFromEnum(CtorEnum.Pop);
    const buildPop = StackCalcFCtorDefs(A).Pop.build;
    const pop_ops = &[_]FOpInfo{
        .{ .op_e = Pop, .op_lam = @bitCast(try buildPop()) },
    };
    return FreeMonad(cfg, F, void).freeM({}, @constCast(pop_ops));
}

fn liftAdd(comptime cfg: anytype) !FreeMonad(cfg, StackCalcF, void) {
    const A = void;
    const F = StackCalcF;

    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(A));
    const Add: FOpEnumInt = @intFromEnum(CtorEnum.Add);
    const buildAdd = StackCalcFCtorDefs(A).Add.build;
    const add_ops = &[_]FOpInfo{
        .{ .op_e = Add, .op_lam = @bitCast(try buildAdd()) },
    };
    return FreeMonad(cfg, F, void).freeM({}, @constCast(add_ops));
}

fn liftMul(comptime cfg: anytype) !FreeMonad(cfg, StackCalcF, void) {
    const A = void;
    const F = StackCalcF;

    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(A));
    const Mul: FOpEnumInt = @intFromEnum(CtorEnum.Mul);
    const buildMul = StackCalcFCtorDefs(A).Mul.build;
    const mul_ops = &[_]FOpInfo{
        .{ .op_e = Mul, .op_lam = @bitCast(try buildMul()) },
    };
    return FreeMonad(cfg, F, void).freeM({}, @constCast(mul_ops));
}

const StateMonadImpl = zcats.StateMonadImpl;
const StateContext = zcats.StateContext;
const MWriterMaybeMonadImpl = zcats.MWriterMaybeMonadImpl;

fn StackCalcFStateNatImpl(comptime cfg: anytype) type {
    const DefaultCtx = StateContext(cfg);
    return struct {
        none: void = {},

        const Self = @This();
        const S = *ArrayList(Int);

        pub const F = StackCalcF;
        pub const G = StateMonadImpl(cfg, S).F;
        pub const Error = Allocator.Error;

        pub fn trans(self: Self, comptime A: type, fa: F(A)) Error!G(A) {
            _ = self;
            switch (fa) {
                .push => {
                    const action_lam = struct {
                        local_fa: F(A),
                        const LamSelf = @This();
                        pub fn deinit(lam_self: LamSelf) void {
                            _ = lam_self;
                        }

                        pub fn call(
                            lam_self: *const LamSelf,
                            s: S,
                        ) DefaultCtx.Error!DefaultCtx.State(S, A).StateAS {
                            // This lambda just as Haskell code:
                            //     \s -> (s ++ [push[0]], push[1])
                            std.debug.print("trans Push s={any}\n", .{s.items});
                            try s.append(lam_self.local_fa.push[0]);
                            std.debug.print("end trans Push s={any}\n", .{s.items});
                            return .{ lam_self.local_fa.push[1].strongRef(), s };
                        }
                    }{ .local_fa = fa };
                    // It is just as Haskell code:
                    //     State $ \s -> (s ++ [push[0]], push[1])
                    return DefaultCtx.mkStateFromLam(action_lam);
                },
                .pop => {
                    const action_lam = struct {
                        local_fa: F(A),
                        const LamSelf = @This();

                        pub fn call(
                            lam_self: *const LamSelf,
                            s: S,
                        ) DefaultCtx.Error!DefaultCtx.State(S, A).StateAS {
                            // This lambda just as Haskell code:
                            //     \s -> (tail s, k)
                            std.debug.print("trans Pop s={any}\n", .{s.items});
                            _ = s.pop();
                            std.debug.print("end trans Pop s={any}\n", .{s.items});
                            return .{ lam_self.local_fa.pop.strongRef(), s };
                        }
                    }{ .local_fa = fa };
                    // It is just as Haskell code:
                    //     State $ \s -> (tail s, k)
                    return DefaultCtx.mkStateFromLam(action_lam);
                },
                .add => {
                    const action_lam = struct {
                        local_fa: F(A),
                        const LamSelf = @This();

                        pub fn call(
                            lam_self: *const LamSelf,
                            s: S,
                        ) DefaultCtx.Error!DefaultCtx.State(S, A).StateAS {
                            // This lambda just as Haskell code:
                            //     \s@(x:y:ts) -> ((x+y):ts, k)
                            std.debug.print("trans Add s={any}\n", .{s.items});
                            const x = s.pop();
                            const y = s.pop();
                            try s.append(x + y);
                            std.debug.print("end trans Add s={any}\n", .{s.items});
                            return .{ lam_self.local_fa.add.strongRef(), s };
                        }
                    }{ .local_fa = fa };
                    // It is just as Haskell code:
                    //     State $ \s@(x:y:ts) -> ((x+y):ts, k)
                    return DefaultCtx.mkStateFromLam(action_lam);
                },
                .mul => {
                    const action_lam = struct {
                        local_fa: F(A),
                        const LamSelf = @This();

                        pub fn call(
                            lam_self: *const LamSelf,
                            s: S,
                        ) DefaultCtx.Error!DefaultCtx.State(S, A).StateAS {
                            // This lambda just as Haskell code:
                            //     \s@(x:y:ts) -> ((x*y):ts, k)
                            std.debug.print("trans Mul s={any}\n", .{s.items});
                            const x = s.pop();
                            const y = s.pop();
                            try s.append(x * y);
                            std.debug.print("end trans Mul s={any}\n", .{s.items});
                            return .{ lam_self.local_fa.mul.strongRef(), s };
                        }
                    }{ .local_fa = fa };
                    // It is just as Haskell code:
                    //     State $ \s@(x:y:ts) -> ((x*y):ts, k)
                    return DefaultCtx.mkStateFromLam(action_lam);
                },
            }
        }
    };
}

const MWriterMaybe = zcats.MWriterMaybe;

pub const StackCalcFShowNatImpl = struct {
    allocator: Allocator,

    const Self = @This();

    pub const F = StackCalcF;
    pub const G = MWriterMaybe(ArrayList(u8));
    pub const Error = Allocator.Error;

    pub fn trans(self: Self, comptime A: type, fa: F(A)) Error!G(A) {
        switch (fa) {
            .push => {
                const push_fmt_str = "Push {any}, ";
                const len = std.fmt.count(push_fmt_str, .{fa.push[0]});
                var array = try ArrayList(u8).initCapacity(self.allocator, len);
                const push_buf = array.addManyAsSliceAssumeCapacity(len);
                _ = std.fmt.bufPrint(push_buf, push_fmt_str, .{fa.push[0]}) catch |err|
                    switch (err) {
                    error.NoSpaceLeft => unreachable, // we just counted the size above
                };
                return .{ .a = fa.push[1], .w = array };
            },
            .pop => {
                const pop_str = "Pop, ";
                var array = try ArrayList(u8).initCapacity(self.allocator, pop_str.len);
                array.appendSliceAssumeCapacity(pop_str);
                return .{ .a = fa.pop, .w = array };
            },
            .add => {
                const add_str = "Add, ";
                var array = try ArrayList(u8).initCapacity(self.allocator, add_str.len);
                array.appendSliceAssumeCapacity(add_str);
                return .{ .a = fa.add, .w = array };
            },
            .mul => {
                const mul_str = "Mul, ";
                var array = try ArrayList(u8).initCapacity(self.allocator, mul_str.len);
                array.appendSliceAssumeCapacity(mul_str);
                return .{ .a = fa.mul, .w = array };
            },
        }
    }
};

var allocator_instance = std.heap.GeneralPurposeAllocator(.{}){};
const g_allocator = allocator_instance.allocator();
const StateS = *ArrayList(Int);

fn cloneStateS(s: StateS) Allocator.Error!StateS {
    return s;
}

fn freeStateS(allocator: Allocator, s: StateS) void {
    _ = allocator;
    _ = s;
}

fn getArrayListStateCfg(comptime T: type, allocator: Allocator) zcats.StateCtxCfg(T) {
    return .{
        .clone_s = &cloneStateS,
        .free_s = &freeStateS,
        .allocator = allocator,
        .error_set = Allocator.Error,
    };
}

fn runStackCalcSample() !void {
    const input1: Int = 42;

    const allocator = g_allocator;
    const F = StackCalcF;
    const cfg = getArrayListStateCfg(StateS, allocator);
    const StackCalcFunctor = Functor(StackCalcFunctorImpl);
    const stack_calc_functor = StackCalcFunctor.init(.{});
    const FreeStackCalcImpl = FreeMonadImpl(cfg, F, StackCalcFunctorImpl);
    const FStateMonad = Monad(FreeStackCalcImpl);
    const freem_monad = FStateMonad.init(.{
        .allocator = allocator,
        .funf_impl = stack_calc_functor,
    });

    const StateMonad = Monad(StateMonadImpl(cfg, StateS));
    const state_monad = StateMonad.init(.{ .allocator = allocator });
    const NatStackCalcFToState = NatTrans(StackCalcFStateNatImpl(cfg));
    const nat_calc_state = NatStackCalcFToState.init(.{});

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatStackCalcToShow = NatTrans(StackCalcFShowNatImpl);
    const nat_calc_show = NatStackCalcToShow.init(.{ .allocator = allocator });

    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: FreeStackCalcImpl,
        param1: u64,

        // intermediate variable
        b: u32 = undefined,

        const Ctx = @This();
        pub const is_pure = false;

        fn deinit(ctx: Ctx) void {
            _ = ctx;
        }

        // the do context struct must has startDo function
        pub fn startDo(impl: *FreeStackCalcImpl) FreeStackCalcImpl.MbType(void) {
            // const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            _ = impl;
            return liftPush(cfg, 3);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *FreeStackCalcImpl, a: u64) FreeStackCalcImpl.MbType(void) {
            _ = impl;
            _ = a;
            return liftPush(cfg, 4);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *FreeStackCalcImpl, a: u64) FreeStackCalcImpl.MbType(void) {
            _ = impl;
            _ = a;
            return liftAdd(cfg);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do3(impl: *FreeStackCalcImpl, a: u64) FreeStackCalcImpl.MbType(void) {
            _ = impl;
            _ = a;
            return liftPush(cfg, 5);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do4(impl: *FreeStackCalcImpl, a: u64) FreeStackCalcImpl.MbType(void) {
            _ = impl;
            _ = a;
            return liftMul(cfg);
        }
    }{ .monad_impl = freem_monad, .param1 = input1 };
    defer do_ctx.deinit();
    var free_state1 = try runDo(&do_ctx);
    defer free_state1.deinit();

    const state1 = try free_state1.foldFree(nat_calc_state, stack_calc_functor, state_monad);
    var init_s = ArrayList(Int).init(allocator);
    defer init_s.deinit();
    const res1_a, const res1_s = try state1.runState(&init_s);
    _ = state1.strongUnref();
    // (42 + 17) / 7 + 42 = 50
    try testing.expectEqual({}, res1_a);
    // s = ctx.b = ctx.param1 = 42
    try testing.expectEqualSlices(Int, &[_]Int{35}, res1_s.items);
    const show_writer1 = try free_state1.foldFree(nat_calc_show, stack_calc_functor, show_monad);
    defer show_writer1.deinit();
    // (42 + 0) / 7 + 42 = 48
    try testing.expectEqual({}, show_writer1.a);
    // s = ctx.b = ctx.param1 = 42
    try testing.expectEqualSlices(u8, "Push 3, Push 4, Add, Push 5, Mul, ", show_writer1.w.items);
}

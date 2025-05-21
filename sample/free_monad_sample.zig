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
const EffectVal = zcats.EffectVal;
var maybe_error = zcats.maybe_error;

const Monoid = zcats.Monoid;
const Functor = zcats.Functor;
const NatTrans = zcats.NatTrans;
const Applicative = zcats.Applicative;
const Monad = zcats.Monad;
const MonadFromImpl = zcats.MonadFromImpl;
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

const Int = std.meta.Int(.signed, @bitSizeOf(usize));

// The Kont is a continuation type
fn StackCalcF(comptime Kont: type) type {
    return union(enum) {
        push: struct { Int, Kont },
        pop: Kont,
        top: *TopLamType,
        add: Kont,
        mul: Kont,

        const Self = @This();
        const cfg = zcats.getDefaultBaseCfg(g_allocator);
        const TopLamType = zcats.ComposableLam(cfg, Int, EffectVal(Error, Kont));

        pub const BaseType = Kont;
        pub const Error: ?type = cfg.errors;
        pub const FunctorImpl = StackCalcFunctorImpl;
        pub const ExistentialType = Int;
        pub const OpCtorDefs = ValidateOpCtorDefs();

        fn ValidateOpCtorDefs() type {
            const op_ctor_defs = StackCalcFCtorDefs(cfg, Kont);
            const CtorEnum = std.meta.DeclEnum(op_ctor_defs);
            const push_e = @intFromEnum(std.meta.activeTag(Self{ .push = undefined }));
            const pop_e = @intFromEnum(std.meta.activeTag(Self{ .pop = undefined }));
            const top_e = @intFromEnum(std.meta.activeTag(Self{ .top = undefined }));
            const add_e = @intFromEnum(std.meta.activeTag(Self{ .add = undefined }));
            const mul_e = @intFromEnum(std.meta.activeTag(Self{ .mul = undefined }));
            // Check if it has same order of {Push, Pop, Add, Mul}
            assert(@intFromEnum(CtorEnum.Push) == push_e);
            assert(@intFromEnum(CtorEnum.Pop) == pop_e);
            assert(@intFromEnum(CtorEnum.Top) == top_e);
            assert(@intFromEnum(CtorEnum.Add) == add_e);
            assert(@intFromEnum(CtorEnum.Mul) == mul_e);
            return op_ctor_defs;
        }

        pub fn deinit(self: Self) void {
            if (self == .top) {
                _ = self.top.strongUnref();
            }
        }
    };
}

const StackCalcFunctorImpl = struct {
    none: void = {},

    const Self = @This();

    /// Constructor Type for Functor, Applicative, Monad, ...
    pub const F = StackCalcF;

    /// Get base type of F(A), it is must just is A.
    pub fn BaseType(comptime StackCalcFA: type) type {
        return StackCalcFA.BaseType;
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
        fa: anytype, // StackCalcF(A)
        comptime free_fn: *const fn (BaseType(@TypeOf(fa))) void,
    ) void {
        switch (fa) {
            .pop, .add, .mul => |a| {
                free_fn(a);
            },
            .push => {
                free_fn(fa.push[1]);
            },
            .top => {},
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
        const A = MapFnInType(@TypeOf(map_fn));
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
            .top => {
                const MapRefLam = struct {
                    map_fn: @TypeOf(map_fn),
                    const MapSelf = @This();
                    pub fn call(map_self: MapSelf, a: std.meta.Child(A)) B {
                        return map_self.map_fn(&a);
                    }
                };

                const top_lam = if (isInplaceMap(K)) fa.top else fa.top.strongRef();
                if (comptime isMapRef(K)) {
                    const map_ref_lam = MapRefLam{ .map_fn = map_fn };
                    return .{ .top = try top_lam.appendLam(map_ref_lam) };
                }
                return .{ .top = try top_lam.appendFn(map_fn) };
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
        const A = MapLamInType(@TypeOf(map_lam));
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
            .top => {
                const MapRefLam = struct {
                    map_lam: @TypeOf(map_lam),
                    const MapSelf = @This();
                    pub fn call(map_self: MapSelf, a: std.meta.Child(A)) B {
                        return map_self.map_lam.call(&a);
                    }
                };

                const top_lam = if (isInplaceMap(K)) fa.top else fa.top.strongRef();
                if (comptime isMapRef(K)) {
                    const map_ref_lam = MapRefLam{ .map_lam = map_lam };
                    return .{ .top = try top_lam.appendLam(map_ref_lam) };
                }
                return .{ .top = try top_lam.appendLam(map_lam) };
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
fn StackCalcFCtorDefs(comptime cfg: anytype, comptime A: type) type {
    const Error = Allocator.Error;

    // Define Op constructor lambdas for StackCalcF
    return struct {
        // The order of Push...Mul must be same as order of push...mul in StackCalcF
        pub const Push = PushLam;
        pub const Pop = PopLam;
        pub const Top = TopLam;
        pub const Add = AddLam;
        pub const Mul = MulLam;

        const SelfCtor = @This();
        const CtorEnum = std.meta.DeclEnum(SelfCtor);
        const Push_E: FOpEnumInt = @intFromEnum(CtorEnum.Push);
        const Pop_E: FOpEnumInt = @intFromEnum(CtorEnum.Pop);
        const Top_E: FOpEnumInt = @intFromEnum(CtorEnum.Top);
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
            lam_ctx: zcats.AnyOpLamCtxType = 0,
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

        const TopLam = extern struct {
            lam_ctx: *TopLamType,

            const Self = @This();
            // This Op is just a function that return type is A
            pub const is_fn_op = true;
            const TopLamType = zcats.ComposableLam(cfg, Int, Error!A);

            pub fn build(action: anytype) Error!Self {
                const info = @typeInfo(@TypeOf(action));
                const is_valid, const action_lam = switch (info) {
                    .@"struct" => .{ true, action },

                    .@"fn" => .{ true, zcats.mapFnToLam(action) },
                    .pointer => if (@typeInfo(info.pointer.child) == .@"fn")
                        .{ true, zcats.mapFnToLam(action) }
                    else
                        .{ false, undefined },
                    else => .{ false, undefined },
                };

                if (!is_valid) {
                    @compileError("Expect action be a function or lambda," ++
                        " found '" ++ @typeName(@TypeOf(action)) ++ "'");
                }

                const top_lam = try TopLamType.create(action_lam);
                return .{ .lam_ctx = top_lam };
            }

            pub fn fpureToFreem(FreeMType: type, fpure: StackCalcF(A)) Error!FreeMType {
                comptime assert(Int == FreeMType.ExistType);
                const impureId = zcats.getImpureIdentityFn(Error, Int);
                const top_lam = try zcats.ComposableLam(cfg, Int, Error!Int).createByFn(impureId);
                return FreeMType.freeFOp(fpure.top, Top_E, .{ .lam_ctx = top_lam });
            }

            pub fn deinit(self: Self) void {
                _ = self.lam_ctx.strongUnref();
            }

            pub fn clone(self: Self) Error!Self {
                return .{ .lam_ctx = self.lam_ctx.strongRef() };
            }

            pub fn call(self: *const Self) StackCalcF(A) {
                return .{ .top = self.lam_ctx.strongRef() };
            }
        };

        const AddLam = extern struct {
            lam_ctx: zcats.AnyOpLamCtxType = 0,
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
            lam_ctx: zcats.AnyOpLamCtxType = 0,
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

    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(cfg, A));
    const Push: FOpEnumInt = @intFromEnum(CtorEnum.Push);
    const buildPush = StackCalcFCtorDefs(cfg, A).Push.build;
    const push_ops = &[_]FOpInfo{
        .{ .op_e = Push, .op_lam = @bitCast(try buildPush(n)) },
    };
    return FreeMonad(cfg, F, void).freeM({}, @constCast(push_ops));
}

fn liftPop(comptime cfg: anytype) !FreeMonad(cfg, StackCalcF, void) {
    const A = void;
    const F = StackCalcF;

    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(cfg, A));
    const Pop: FOpEnumInt = @intFromEnum(CtorEnum.Pop);
    const buildPop = StackCalcFCtorDefs(cfg, A).Pop.build;
    const pop_ops = &[_]FOpInfo{
        .{ .op_e = Pop, .op_lam = @bitCast(try buildPop()) },
    };
    return FreeMonad(cfg, F, void).freeM({}, @constCast(pop_ops));
}

fn LiftTopType(comptime cfg: anytype, comptime ActionType: type) type {
    const info = @typeInfo(ActionType);
    switch (info) {
        .@"struct" => {
            const A = MapLamRetType(ActionType);
            const has_err, const _A = isErrorUnionOrVal(A);
            _ = has_err;
            return FreeMonad(cfg, StackCalcF, _A);
        },

        .@"fn" => {
            const A = MapFnRetType(ActionType);
            const has_err, const _A = isErrorUnionOrVal(A);
            _ = has_err;
            return FreeMonad(cfg, StackCalcF, _A);
        },
        .pointer => if (@typeInfo(info.pointer.child) == .@"fn") {
            const A = MapFnRetType(ActionType);
            const has_err, const _A = isErrorUnionOrVal(A);
            _ = has_err;
            return FreeMonad(cfg, StackCalcF, _A);
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

pub fn liftTop(comptime cfg: anytype) !FreeMonad(cfg, StackCalcF, Int) {
    const Error = cfg.errors;
    const F = StackCalcF;
    const ExistType = zcats.GetExistentialType(F);
    comptime assert(ExistType == Int);
    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(cfg, Int));
    const Top: FOpEnumInt = @intFromEnum(CtorEnum.Top);
    const buildTop = StackCalcFCtorDefs(cfg, ExistType).Top.build;

    const action_lam = zcats.getEffectIdentityLam(Error, Int);
    const comp_action_lam = try zcats.ComposableLam(cfg, Int, EffectVal(Error, Int)).create(action_lam);
    const top_lam = try comp_action_lam.appendFn(FreeMonad(cfg, F, Int).pureM);
    defer _ = top_lam.strongUnref();
    return FreeMonad(cfg, F, Int).freeFOp(top_lam, Top, try buildTop(zcats.getEffectIdentityFn(Error, Int)));
}

fn liftAdd(comptime cfg: anytype) !FreeMonad(cfg, StackCalcF, void) {
    const A = void;
    const F = StackCalcF;

    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(cfg, A));
    const Add: FOpEnumInt = @intFromEnum(CtorEnum.Add);
    const buildAdd = StackCalcFCtorDefs(cfg, A).Add.build;
    const add_ops = &[_]FOpInfo{
        .{ .op_e = Add, .op_lam = @bitCast(try buildAdd()) },
    };
    return FreeMonad(cfg, F, void).freeM({}, @constCast(add_ops));
}

fn liftMul(comptime cfg: anytype) !FreeMonad(cfg, StackCalcF, void) {
    const A = void;
    const F = StackCalcF;

    const CtorEnum = std.meta.DeclEnum(StackCalcFCtorDefs(cfg, A));
    const Mul: FOpEnumInt = @intFromEnum(CtorEnum.Mul);
    const buildMul = StackCalcFCtorDefs(cfg, A).Mul.build;
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
        pub const Error: ?type = Allocator.Error;

        pub fn trans(self: Self, comptime A: type, fa: F(A)) Error.?!G(A) {
            _ = self;
            switch (fa) {
                .push => {
                    const action_lam = struct {
                        local_n: Int,
                        local_k: A,
                        const LamSelf = @This();
                        pub fn deinit(lam_self: LamSelf) void {
                            _ = lam_self.local_k.strongUnref();
                        }

                        pub fn call(
                            lam_self: *const LamSelf,
                            s: S,
                        ) EffectVal(DefaultCtx.Error, DefaultCtx.State(S, A).StateAS) {
                            // This lambda just as Haskell code:
                            //     \s -> (k, a:s)
                            try s.append(lam_self.local_n); // s.push(n)
                            return .{ lam_self.local_k, s };
                        }
                    }{ .local_n = fa.push[0], .local_k = fa.push[1].strongRef() };
                    // It is just as Haskell code:
                    //     State $ \s -> (k, a:s)
                    return DefaultCtx.mkStateFromLam(action_lam);
                },
                .pop => {
                    const action_lam = struct {
                        local_k: A,
                        const LamSelf = @This();
                        pub fn deinit(lam_self: LamSelf) void {
                            _ = lam_self.local_k.strongUnref();
                        }

                        pub fn call(
                            lam_self: *const LamSelf,
                            s: S,
                        ) EffectVal(DefaultCtx.Error, DefaultCtx.State(S, A).StateAS) {
                            // This lambda just as Haskell code:
                            //     \s -> (k, tail s)
                            _ = s.pop() orelse @panic("Pop empty stack in calculator!");
                            return .{ lam_self.local_k, s };
                        }
                    }{ .local_k = fa.pop.strongRef() };
                    // It is just as Haskell code:
                    //     State $ \s -> (k, tail s)
                    return DefaultCtx.mkStateFromLam(action_lam);
                },
                .top => {
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
                            //     \s -> (k (head s), s)
                            if (s.items.len == 0)
                                @panic("Top from empty stack in calculator!");
                            return .{ try lam_self.local_fa.top.call(s.items[s.items.len - 1]), s };
                        }
                    }{ .local_fa = .{ .top = fa.top.strongRef() } };
                    // It is just as Haskell code:
                    //     State $ \s -> (k (head s), s)
                    return DefaultCtx.mkStateFromLam(action_lam);
                },
                .add => {
                    const action_lam = struct {
                        local_k: A,
                        const LamSelf = @This();
                        pub fn deinit(lam_self: LamSelf) void {
                            _ = lam_self.local_k.strongUnref();
                        }

                        pub fn call(
                            lam_self: *const LamSelf,
                            s: S,
                        ) EffectVal(DefaultCtx.Error, DefaultCtx.State(S, A).StateAS) {
                            // This lambda just as Haskell code:
                            //     \s@(x:y:ts) -> (k, (x+y):ts)
                            const x = s.pop().?;
                            const y = s.pop().?;
                            try s.append(x + y); // s.push(x + y)
                            return .{ lam_self.local_k, s };
                        }
                    }{ .local_k = fa.add.strongRef() };
                    // It is just as Haskell code:
                    //     State $ \s@(x:y:ts) -> (k, (x+y):ts)
                    return DefaultCtx.mkStateFromLam(action_lam);
                },
                .mul => {
                    const action_lam = struct {
                        local_k: A,
                        const LamSelf = @This();
                        pub fn deinit(lam_self: LamSelf) void {
                            _ = lam_self.local_k.strongUnref();
                        }

                        pub fn call(
                            lam_self: *const LamSelf,
                            s: S,
                        ) EffectVal(DefaultCtx.Error, DefaultCtx.State(S, A).StateAS) {
                            // This lambda just as Haskell code:
                            //     \s@(x:y:ts) -> (k, (x*y):ts)
                            const x = s.pop().?;
                            const y = s.pop().?;
                            try s.append(x * y); // s.push(x * y)
                            return .{ lam_self.local_k, s };
                        }
                    }{ .local_k = fa.mul.strongRef() };
                    // It is just as Haskell code:
                    //     State $ \s@(x:y:ts) -> (k, (x*y):ts)
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
    pub const Error: ?type = Allocator.Error;

    pub fn trans(self: Self, comptime A: type, fa: F(A)) Error.?!G(A) {
        switch (fa) {
            .push => {
                const push_fmt_str = "Push {any}, ";
                const len = std.fmt.count(push_fmt_str, .{fa.push[0]});
                var array = try ArrayList(u8).initCapacity(self.allocator, @intCast(len));
                const push_buf = array.addManyAsSliceAssumeCapacity(@intCast(len));
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
            .top => {
                const top_str = "Top, ";
                var array = try ArrayList(u8).initCapacity(self.allocator, top_str.len);
                array.appendSliceAssumeCapacity(top_str);
                return .{ .a = try fa.top.call(0), .w = array };
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
        .errors = Allocator.Error,
    };
}

fn runStackCalcSample() !void {
    const input1: Int = 42;

    const allocator = g_allocator;
    defer _ = allocator_instance.deinit();
    const F = StackCalcF;
    const cfg = getArrayListStateCfg(StateS, allocator);
    const StackCalcFunctor = Functor(F);
    const stack_calc_functor = StackCalcFunctor.InstanceImpl{};
    const FStateMonad = Monad(zcats.FreeM(cfg, F));
    const freem_monad = FStateMonad.InstanceImpl{
        .allocator = allocator,
        .funf_impl = stack_calc_functor,
    };
    const FreeStackCalcImpl = @TypeOf(freem_monad);

    const StateMonad = Monad(zcats.StateContext(cfg).StateM(StateS));
    const state_monad = StateMonad.InstanceImpl{ .allocator = allocator };
    const NatStackCalcFToState = NatTrans(StackCalcFStateNatImpl(cfg));
    const nat_calc_state = NatStackCalcFToState.InstanceImpl{};

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = MonadFromImpl(ShowMonadImpl);
    const ArrayMonoid = Monoid(ArrayList(u8));
    const array_monoid = ArrayMonoid.InstanceImpl{ .allocator = allocator };
    const show_monad = ShowMonad.InstanceImpl{ .monoid_impl = array_monoid };
    const NatStackCalcToShow = NatTrans(StackCalcFShowNatImpl);
    const nat_calc_show = NatStackCalcToShow.InstanceImpl{ .allocator = allocator };

    // This do block is just as Haskell code:
    // calc = do
    //   push 3
    //   push 4
    //   add
    //   push 5
    //   mul
    //   x <- top
    //   pop
    //   pure x
    var do_ctx = struct {
        // It is must to define monad_impl for support do syntax.
        monad_impl: FreeStackCalcImpl,
        param1: u64,

        // intermediate variable
        x: Int = undefined,

        const Ctx = @This();
        pub const Error: ?type = maybe_error.mappend(null, FreeStackCalcImpl.Error);

        fn deinit(ctx: Ctx) void {
            _ = ctx;
        }

        // the do context struct must has startDo function
        pub fn startDo(impl: *FreeStackCalcImpl) FreeStackCalcImpl.MbType(void) {
            // const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            _ = impl;
            // push 3
            return liftPush(cfg, 3);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do1(impl: *FreeStackCalcImpl, a: void) FreeStackCalcImpl.MbType(void) {
            _ = impl;
            _ = a;
            // push 4
            return liftPush(cfg, 4);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do2(impl: *FreeStackCalcImpl, a: void) FreeStackCalcImpl.MbType(void) {
            _ = impl;
            _ = a;
            // add
            return liftAdd(cfg);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do3(impl: *FreeStackCalcImpl, a: void) FreeStackCalcImpl.MbType(void) {
            _ = impl;
            _ = a;
            // push 5
            return liftPush(cfg, 5);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do4(impl: *FreeStackCalcImpl, a: void) FreeStackCalcImpl.MbType(void) {
            _ = impl;
            _ = a;
            // mul
            return liftMul(cfg);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do5(impl: *FreeStackCalcImpl, a: void) FreeStackCalcImpl.MbType(Int) {
            _ = impl;
            _ = a;
            // top
            return liftTop(cfg);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do6(impl: *FreeStackCalcImpl, a: Int) FreeStackCalcImpl.MbType(void) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            // x <- top
            ctx.x = a;
            // pop
            return liftPop(cfg);
        }

        // the name of other do step function must be starts with "do" string
        pub fn do7(impl: *FreeStackCalcImpl, a: void) FreeStackCalcImpl.MbType(Int) {
            const ctx: *Ctx = @alignCast(@fieldParentPtr("monad_impl", impl));
            _ = a;
            // return x
            return impl.pure(ctx.x);
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
    std.debug.print("run StackCalc result is: ({any}, {any})\n", .{ res1_a, res1_s.items });
    const show_writer1 = try free_state1.foldFree(nat_calc_show, stack_calc_functor, show_monad);
    defer show_writer1.deinit();
    std.debug.print("StackCalc expression is: \"{s}\"\n", .{show_writer1.w.items});
}

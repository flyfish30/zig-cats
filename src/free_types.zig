//! Define some types to implement Free Structure in Haskell, such as Free Monad,
//! Free Applicative, etc.

const std = @import("std");
const base = @import("base.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const maybe = @import("maybe.zig");
const arraym = @import("array_list_monad.zig");
const state = @import("state.zig");
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
const MaybeMonadImpl = maybe.MaybeMonadImpl;
const ArrayListMonadImpl = arraym.ArrayListMonadImpl;

const FunctorFxTypes = functor.FunctorFxTypes;
const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
const MonadFxTypes = monad.MonadFxTypes;
const runDo = monad.runDo;

const DEFAULT_LEN: usize = 8;

// The OpLam is a natural transformation between Id a annd F a.
pub const FOpEnumInt = u16;

// The AnyOpLam is a dummy type for specify OpLam
const AnyOpLam = extern struct {
    lam_ctx: u64,
    const Self = @This();
    pub fn call(self: Self) void {
        _ = self;
    }
};

/// The build information of operator in F for FreeMonad(F, A)
pub const FOpInfo = struct {
    op_e: FOpEnumInt,
    // TODO: Add FOpKind for normal Op and function Op
    // op_kind: FOpKind
    op_lam: AnyOpLam,
};

pub fn toAnyOpLam(op_lam: anytype) AnyOpLam {
    const OpLam = @TypeOf(op_lam);
    comptime assert(@sizeOf(OpLam) == @sizeOf(AnyOpLam));
    var any_op_lam: AnyOpLam = undefined;
    @memcpy(std.mem.asBytes(&any_op_lam), std.mem.asBytes(&op_lam));
    return any_op_lam;
}

pub fn toSpecificOpLam(comptime OpLam: type, any_op_lam: AnyOpLam) OpLam {
    comptime assert(@sizeOf(OpLam) == @sizeOf(AnyOpLam));
    var op_lam: OpLam = undefined;
    @memcpy(std.mem.asBytes(&op_lam), std.mem.asBytes(&any_op_lam));
    return op_lam;
}

/// This is type constructor of Free Monad, the parameter F must be a Functor,
/// and all operator constructors of F must take only one parameter.
/// If you need a operator constructor with multiple parameters, you can curry it
/// into multiple operator constructors that take one parameter.
pub fn FreeMonad(comptime cfg: anytype, comptime F: TCtor, comptime A: type) type {
    return FreeM(cfg, F)(A);
}

/// The type function FreeM is currying form of type constructor FreeMonad.
pub fn FreeM(comptime in_cfg: anytype, comptime F: TCtor) TCtor {
    return struct {
        fn FreeF(comptime A: type) type {
            return union(enum) {
                /// The FreeMonad(F, A) type that defined by Haskell is
                ///     data Free f a = Pure a
                ///                   | Free (f (Free f a))
                /// The value Free (f2 (Free (f1 (Free (f0 pure_m))))) layout is
                /// ( pure_m, [f0, f1, f2] )
                //

                /// pure value of FreeMonad(F, A)
                pure_m: A,

                /// X to FreeMonad(F, A) transformation function pair with build
                /// information f0 for operator that is just a function operator such
                /// as: GetF (S -> X). The f0 is a operator consturctor for functor F
                /// with type: () -> F X
                /// This FreeMonad(F, A) with layout:
                ///         ( x_to_freem, f0 )
                /// In yoneda lemma, it is equivalent to F(FreeMonad(F, A)) by
                /// equivalence relationship in coyoneda form:
                ///    exist x. (x -> a) (F x)  <==> F a
                /// This value is defined for the FreeMonad(F, A) that has a function
                /// operator.
                /// For example, the GetF in StateF that defined in bellow is a
                /// function operator.
                ///     data StateF s a = GetF (s -> a)
                ///                     | PutF s a
                free_fop: struct { *XToFreeFALam, FOpInfo },

                /// Tuple of (pure FreeMonad(F, A), reversed f list), every f is just a
                /// build information of operator in F.
                free_m: struct { *Self, ArrayList(FOpInfo) },

                const Self = @This();
                pub const BaseType = A;
                pub const Error = Allocator.Error;
                pub const cfg = in_cfg;
                pub const ExistType = if (@hasField(@TypeOf(cfg), "ExistentialType"))
                    cfg.ExistentialType
                else
                    GetExistentialType(F);
                const XToFreeFALam = base.ComposableLam(cfg, ExistType, Error!Self);

                pub fn deinit(self: Self) void {
                    if (self == .free_m) {
                        const allocator = cfg.allocator;
                        const fa_op_ctors = GetOpCtors(F, A);
                        for (self.free_m[1].items) |op_info| {
                            const op_ctor_info = fa_op_ctors[op_info.op_e];
                            op_ctor_info.deinitOpCtor(op_info.op_lam);
                        }
                        self.free_m[1].deinit();

                        self.free_m[0].deinit();
                        allocator.destroy(self.free_m[0]);
                    } else if (self == .free_fop) {
                        _ = self.free_fop[0].strongUnref();
                        const op_info = self.free_fop[1];
                        const fa_op_ctors = GetOpCtors(F, A);
                        const op_ctor_info = fa_op_ctors[op_info.op_e];
                        op_ctor_info.deinitOpCtor(op_info.op_lam);
                    }
                }

                pub fn pureM(a: A) Self {
                    return .{ .pure_m = a };
                }

                /// Create a FreeMoand(F, A) that has only one function operator
                pub fn freeFOp(
                    x_to_freem: anytype,
                    e: FOpEnumInt,
                    fop_lam: anytype,
                ) !Self {
                    // TODO: add a check assume the f is a function operator
                    // assert(f.op_kind == OpFunction)
                    const XToFreemType = @TypeOf(x_to_freem);
                    if (XToFreemType == *XToFreeFALam) {
                        const fop = .{ .op_e = e, .op_lam = toAnyOpLam(fop_lam) };
                        return .{ .free_fop = .{ x_to_freem.strongRef(), fop } };
                    }

                    const info = @typeInfo(@TypeOf(x_to_freem));
                    const is_valid, const x_to_freem_lam = switch (info) {
                        .Struct => .{ true, x_to_freem },

                        .Fn => .{ true, base.mapFnToLam(x_to_freem) },
                        .Pointer => if (@typeInfo(info.Pointer.child) == .Fn)
                            .{ true, base.mapFnToLam(x_to_freem) }
                        else
                            .{ false, undefined },
                        else => .{ false, undefined },
                    };

                    if (!is_valid) {
                        @compileLog("freeFOp XToFreeFALam type: " ++ @typeName(XToFreeFALam));
                        @compileError("Expect x_to_freem be a function or lambda," ++
                            " found '" ++ @typeName(@TypeOf(x_to_freem)) ++ "'");
                    }

                    const X = MapLamInType(@TypeOf(x_to_freem_lam));
                    const FX = MapLamRetType(@TypeOf(fop_lam));
                    const has_err, const _FX = comptime isErrorUnionOrVal(FX);
                    _ = has_err;
                    comptime assert(X == _FX.BaseType);

                    const fop = .{ .op_e = e, .op_lam = toAnyOpLam(fop_lam) };
                    return .{ .free_fop = .{ try XToFreeFALam.create(x_to_freem_lam), fop } };
                }

                pub fn freeM(a: A, fs: []FOpInfo) !Self {
                    const allocator = cfg.allocator;
                    const new_pure_m = try allocator.create(Self);
                    new_pure_m.* = .{ .pure_m = a };
                    var flist = try ArrayList(FOpInfo).initCapacity(allocator, fs.len);
                    flist.appendSliceAssumeCapacity(fs);
                    return .{ .free_m = .{ new_pure_m, flist } };
                }

                fn freeFPure(fpure: anytype) !Self {
                    const FpureType = @TypeOf(fpure);
                    comptime assert(Self == FpureType.BaseType);

                    const fx_op_ctors = GetOpCtors(F, Self);
                    const ctor_e = std.meta.activeTag(fpure);
                    const op_e = @intFromEnum(ctor_e);
                    const op_ctor_info = fx_op_ctors[op_e];
                    return try op_ctor_info.fpureToFreem(Self, fpure);
                }

                pub fn liftFree(f_impl: anytype, fa: anytype) !Self {
                    const fpure = try f_impl.fmap(.NewValMap, pureM, fa);
                    defer fpure.deinit();
                    return freeFPure(fpure);
                }

                // This function has move semantics, all value in self move to new self.
                pub fn appendFOp(self: Self, f: FOpInfo) !Self {
                    const allocator = cfg.allocator;
                    if (self == .pure_m) {
                        var flist = try ArrayList(FOpInfo).initCapacity(allocator, DEFAULT_LEN);
                        flist.appendAssumeCapacity(f);
                        const new_pure_m = try allocator.create(Self);
                        new_pure_m.* = .{ .pure_m = self.pure_m };
                        return .{ .free_m = .{ new_pure_m, flist } };
                    } else if (self == .free_fop) {
                        var flist = try ArrayList(FOpInfo).initCapacity(allocator, DEFAULT_LEN);
                        flist.appendAssumeCapacity(f);
                        const new_pure_m = try allocator.create(Self);
                        new_pure_m.* = .{ .free_fop = self.free_fop };
                        return .{ .free_m = .{ new_pure_m, flist } };
                    } else {
                        var flist = self.free_m[1];
                        try flist.append(f);
                        return .{ .free_m = .{ self.free_m[0], flist } };
                    }
                }

                // This function has move semantics, all value in self move to new self.
                pub fn appendFOps(self: Self, fs: []const FOpInfo) !Self {
                    const allocator = cfg.allocator;
                    if (self == .pure_m) {
                        var flist = try ArrayList(FOpInfo).initCapacity(allocator, fs.len);
                        flist.appendSliceAssumeCapacity(fs);
                        const new_pure_m = try allocator.create(Self);
                        new_pure_m.* = .{ .pure_m = self.pure_m };
                        return .{ .free_m = .{ new_pure_m, flist } };
                    } else if (self == .free_fop) {
                        var flist = try ArrayList(FOpInfo).initCapacity(allocator, fs.len);
                        flist.appendSliceAssumeCapacity(fs);
                        const new_pure_m = try allocator.create(Self);
                        new_pure_m.* = .{ .free_fop = self.free_fop };
                        return .{ .free_m = .{ new_pure_m, flist } };
                    } else {
                        var flist = self.free_m[1];
                        try flist.appendSlice(fs);
                        return .{ .free_m = .{ self.free_m[0], flist } };
                    }
                }

                pub fn cloneFOps(self: Self) !ArrayList(FOpInfo) {
                    const len = self.free_m[1].items.len;
                    var new_flist = try ArrayList(FOpInfo).initCapacity(cfg.allocator, len);
                    const new_items = new_flist.addManyAtAssumeCapacity(0, len);
                    try self.cloneFOpsToSlice(new_items);
                    return new_flist;
                }

                pub fn cloneFOpsToSlice(self: Self, fops: []FOpInfo) !void {
                    const len = self.free_m[1].items.len;
                    assert(len == fops.len);
                    const fa_op_ctors = GetOpCtors(F, A);
                    for (self.free_m[1].items, fops) |op_info, *new_op_info| {
                        const op_ctor_info = fa_op_ctors[op_info.op_e];
                        const new_op_lam = try op_ctor_info.tryCloneOpCtor(op_info.op_lam);
                        new_op_info.* = .{
                            .op_e = op_info.op_e,
                            .op_lam = new_op_lam orelse op_info.op_lam,
                        };
                    }
                }

                pub fn copyOrCloneFOp(fop: FOpInfo) !FOpInfo {
                    const op_info = fop;
                    const fa_op_ctors = GetOpCtors(F, A);
                    const op_ctor_info = fa_op_ctors[op_info.op_e];
                    const new_op_lam = try op_ctor_info.tryCloneOpCtor(op_info.op_lam);
                    return .{
                        .op_e = op_info.op_e,
                        .op_lam = new_op_lam orelse op_info.op_lam,
                    };
                }

                /// Tear down a FreeMonad(F, A) using iteration.
                pub fn iter(self: Self, f_impl: anytype, f: *const fn (F(A)) A) Error!A {
                    if (self == .pure_m) {
                        return self.pure_m;
                    } else if (self == .free_fop) {
                        const op_info = self.free_fop[1];
                        const fx_op_ctors = GetOpCtors(F, ExistType);
                        const op_ctor_info = fx_op_ctors[op_info.op_e];
                        const fx = try op_ctor_info.callOpCtor(
                            op_info.op_lam,
                            @constCast(&[_]ExistType{}),
                        );

                        const FImpl = @TypeOf(f_impl);
                        // iter inner freem
                        const inner_iter = struct {
                            iter_fimpl: FImpl,
                            iter_f: *const fn (F(A)) A,

                            const SelfIter = @This();
                            pub fn call(self_iter: *const SelfIter, freem: Self) Error!A {
                                // recusive call iter for inner free monad
                                defer freem.deinit();
                                return freem.iter(self_iter.iter_fimpl, self_iter.iter_f);
                            }
                        }{ .iter_fimpl = f_impl, .iter_f = f };

                        const x_to_freem = self.free_fop[0].strongRef();
                        const comp_iter = try x_to_freem.appendLam(inner_iter);
                        const fa = try f_impl.fmapLam(.InplaceMap, comp_iter, fx);
                        _ = comp_iter.strongUnref();
                        defer base.deinitOrUnref(fa);
                        return f(fa);
                    }

                    const fa_op_ctors = GetOpCtors(F, A);
                    var acc_a = if (self.free_m[0].* == .pure_m)
                        self.free_m[0].pure_m
                    else
                        try self.free_m[0].iter(f_impl, f);
                    for (self.free_m[1].items) |op_info| {
                        const op_ctor_info = fa_op_ctors[op_info.op_e];
                        const fa = try op_ctor_info.callOpCtor(
                            op_info.op_lam,
                            @constCast(&[_]A{acc_a}),
                        );
                        acc_a = f(fa);
                    }
                    return acc_a;
                }

                // pub fn hoistFree(
                //     self: Self,
                //     comptime NatImpl: type,
                //     nat_impl: NatImpl,
                // ) FreeMonad(cfg, NatImpl.G, A) {
                //     comptime assert(F == NatImpl.F);
                //     if (self == .pure_m) {
                //         return .{ .pure_m = self.pure_m };
                //     }

                //     const fa_op_ctors = GetOpCtors(F, A);
                //     const allocator = self.free_m[1].allocator;
                //     const new_pure_m = try allocator.create(Self);
                //     new_pure_m.* = .{ .pure_m = self.free_m[0].pure_m.* };
                //     const fs = self.free_m[1].items;
                //     var flist = try ArrayList(FOpInfo).initCapacity(allocator, fs.len);
                //     for (fs) |ctor_idx| {
                //         const op_ctor_info = fa_op_ctors[ctor_idx];
                //         flist.appendAssumeCapacity(compose(nat_impl.trans, origin_f));
                //     }
                //     return .{ .free_m = .{ new_pure_m, flist } };
                // }

                /// Evaluate a FreeMonad(F, A) to a Monad M(A) by given a natural
                /// transformation of F and M. This is equivalent to a monad homomorphism
                /// of FreeMoand(F, A) to M(A).
                /// Parameter nat_impl is a natural transformation instance for translate
                /// F to M.
                /// Parameter f_impl is a functor instance for functor F.
                /// Parameter m_impl is a monad instance for Monad M.
                pub fn foldFree(
                    self: Self,
                    nat_impl: anytype,
                    f_impl: anytype,
                    m_impl: anytype,
                ) @TypeOf(m_impl).MbType(A) {
                    const NatImpl = @TypeOf(nat_impl);
                    const FImpl = @TypeOf(f_impl);
                    const MImpl = @TypeOf(m_impl);
                    comptime assert(F == NatImpl.F);
                    comptime assert(MImpl.F == NatImpl.G);
                    const FoldLam = struct {
                        nat_impl: NatImpl,
                        f_impl: FImpl,
                        m_impl: MImpl,
                        const SelfLam = @This();
                        pub fn call(self_lam: *const SelfLam, freem: Self) MImpl.MbType(A) {
                            // recusive call foldFree for inner free monad
                            defer freem.deinit();
                            return foldFree(
                                freem,
                                self_lam.nat_impl,
                                self_lam.f_impl,
                                self_lam.m_impl,
                            );
                        }
                    };

                    if (self == .pure_m) {
                        return @constCast(&m_impl).pure(self.pure_m);
                    } else if (self == .free_fop) {
                        const op_info = self.free_fop[1];
                        const fx_op_ctors = GetOpCtors(F, ExistType);
                        const op_ctor_info = fx_op_ctors[op_info.op_e];
                        // The fx is a function operator, such as:
                        //     GetF (S -> X)
                        const fx = try op_ctor_info.callOpCtor(
                            op_info.op_lam,
                            @constCast(&[_]ExistType{}),
                        );

                        const inner_fold = FoldLam{
                            .nat_impl = nat_impl,
                            .f_impl = f_impl,
                            .m_impl = m_impl,
                        };
                        // Because the appendLam will consume the x_to_freem, so we
                        // should add a reference for x_to_freem.
                        const x_to_freem = self.free_fop[0].strongRef();
                        const comp_fold = try x_to_freem.appendLam(inner_fold);
                        const f_acc_m = try f_impl.fmapLam(.InplaceMap, comp_fold, fx);
                        const m_acc_m = try nat_impl.trans(MImpl.F(A), f_acc_m);
                        _ = comp_fold.strongUnref();
                        base.deinitOrUnref(f_acc_m);
                        defer MImpl.deinitFa(m_acc_m, base.getDeinitOrUnref(MImpl.F(A)));
                        return try @constCast(&m_impl).join(A, m_acc_m);
                    }

                    var acc_m = if (self.free_m[0].* == .pure_m)
                        try @constCast(&m_impl).pure(self.free_m[0].pure_m)
                    else
                        try self.free_m[0].foldFree(nat_impl, f_impl, m_impl);
                    for (self.free_m[1].items) |op_info| {
                        const fm_op_ctors = GetOpCtors(F, MImpl.F(A));
                        const op_ctor_info = fm_op_ctors[op_info.op_e];
                        const f_acc_m = try op_ctor_info.callOpCtor(
                            op_info.op_lam,
                            @constCast(&[_]MImpl.F(A){acc_m}),
                        );
                        defer base.deinitOrUnref(f_acc_m);
                        const m_acc_m = try nat_impl.trans(MImpl.F(A), f_acc_m);
                        defer MImpl.deinitFa(m_acc_m, base.getDeinitOrUnref(MImpl.F(A)));
                        acc_m = try @constCast(&m_impl).join(A, m_acc_m);
                    }
                    return acc_m;
                }
            };
        }
    }.FreeF;
}

pub fn GetExistentialType(comptime F: TCtor) type {
    comptime {
        const A = void;
        switch (@typeInfo(F(A))) {
            .Struct, .Enum, .Union, .Opaque => {
                if (@hasDecl(F(A), "ExistentialType")) {
                    return F(A).ExistentialType;
                }
            },
            else => {},
        }

        const mapExistTypes = std.StaticStringMap(type).initComptime(.{
            .{ @typeName(Maybe(A)), MaybeExistentialType },
        });

        const exist_type = mapExistTypes.get(@typeName(F(A)));
        if (exist_type == null) {
            @compileError("The customered Functor(" ++ @typeName(F(A)) ++ ") must has ExistentialType!");
        }
        return exist_type.?;
    }
}

const MaybeExistentialType = u32;

fn GetCtorDefs(comptime F: TCtor, comptime A: type) type {
    comptime {
        switch (@typeInfo(F(A))) {
            .Struct, .Enum, .Union, .Opaque => {
                if (@hasDecl(F(A), "OpCtorDefs")) {
                    return F(A).OpCtorDefs;
                }
            },
            else => {},
        }

        const mapCtorDefs = std.StaticStringMap(type).initComptime(.{
            .{ @typeName(Maybe(A)), MaybeCtorDefs(A) },
        });

        const ctor_defs = mapCtorDefs.get(@typeName(F(A)));
        if (ctor_defs == null) {
            @compileError("The customered Functor(" ++ @typeName(F(A)) ++ ") must has OpCtorDefs!");
        }
        return ctor_defs.?;
    }
}

fn OpCtorsType(comptime F: TCtor, comptime A: type) type {
    const OpCtorDefs = GetCtorDefs(F, A);
    const CtorEnum = std.meta.DeclEnum(OpCtorDefs);
    const enum_fields = std.meta.fields(CtorEnum);
    return [enum_fields.len]OpCtorInfo(A, CtorEnum, OpCtorDefs);
}

fn OpCtorInfo(
    comptime A: type,
    comptime OpCtorE: type,
    comptime OpDefs: type,
) type {
    const first_op_e = @as(OpCtorE, @enumFromInt(0));
    const FirstOpLam = @field(OpDefs, @tagName(first_op_e));
    const first_fn_info = @typeInfo(@TypeOf(FirstOpLam.call));
    const OpCtorRetType = first_fn_info.Fn.return_type.?;
    return struct {
        ctor_e: OpCtorE,
        params_len: u8,

        const Self = @This();
        pub fn callOpCtor(self: Self, op_lam: AnyOpLam, as: []A) !OpCtorRetType {
            switch (self.ctor_e) {
                inline else => |e| {
                    // std.debug.print("call OpCtor enum: {any}\n", .{e});
                    // std.debug.print(
                    //     "as.len = {d}, params_len = {d}\n",
                    //     .{ as.len, self.params_len },
                    // );
                    if (self.params_len > 0) {
                        std.debug.assert(as.len == self.params_len);
                    } else {
                        std.debug.assert(as.len == 0 or as.len == 1);
                        if (as.len == 1) {
                            base.deinitOrUnref(as[0]);
                        }
                    }
                    const OpLam = @field(OpDefs, @tagName(e));
                    const Args = std.meta.ArgsTuple(@TypeOf(OpLam.call));
                    var args: Args = undefined;
                    const args_fields = std.meta.fields(Args);
                    assert(args_fields.len - 1 == self.params_len);
                    // first parameter is lambda self
                    if (@typeInfo(OpLam).Struct.layout == .auto) {
                        args[0] = &toSpecificOpLam(OpLam, op_lam);
                    } else {
                        args[0] = @constCast(&@as(OpLam, @bitCast(op_lam)));
                    }
                    comptime var i = 1;
                    inline while (i < @typeInfo(Args).Struct.fields.len) : (i += 1) {
                        args[i] = as[i - 1];
                    }
                    return @call(.auto, OpLam.call, args);
                },
            }
        }

        pub fn deinitOpCtor(self: Self, op_lam: AnyOpLam) void {
            switch (self.ctor_e) {
                inline else => |e| {
                    // std.debug.print("deinit OpCtor enum: {any}\n", .{e});
                    const OpLam = @field(OpDefs, @tagName(e));
                    const spec_op_lam = if (@typeInfo(OpLam).Struct.layout == .auto)
                        &toSpecificOpLam(OpLam, op_lam)
                    else
                        @constCast(&@as(OpLam, @bitCast(op_lam)));
                    return spec_op_lam.deinit();
                },
            }
        }

        pub fn tryCloneOpCtor(self: Self, op_lam: AnyOpLam) !?AnyOpLam {
            switch (self.ctor_e) {
                inline else => |e| {
                    // std.debug.print("clone OpCtor enum: {any}\n", .{e});
                    const OpLam = @field(OpDefs, @tagName(e));
                    const spec_op_lam = if (@typeInfo(OpLam).Struct.layout == .auto)
                        &toSpecificOpLam(OpLam, op_lam)
                    else
                        @constCast(&@as(OpLam, @bitCast(op_lam)));

                    if (@hasDecl(OpLam, "clone")) {
                        const new_op_lam = try spec_op_lam.clone();
                        if (@typeInfo(OpLam).Struct.layout == .auto) {
                            return toAnyOpLam(new_op_lam);
                        } else {
                            return @as(AnyOpLam, @bitCast(new_op_lam));
                        }
                    }
                    return null;
                },
            }
        }

        pub fn fpureToFreem(self: Self, comptime FreeMType: type, fpure: anytype) !FreeMType {
            switch (self.ctor_e) {
                inline else => |e| {
                    // std.debug.print("fpureToFreem OpCtor enum: {any}\n", .{e});
                    const OpLam = @field(OpDefs, @tagName(e));
                    if (!@hasDecl(OpLam, "fpureToFreem")) {
                        @compileError("The functor's constuctor '" ++ @typeName(OpLam) ++
                            "' can not be lifted to a Free Monad");
                    }
                    return @call(.auto, OpLam.fpureToFreem, .{ FreeMType, fpure });
                },
            }
        }
    };
}

pub fn GetOpCtors(
    comptime F: TCtor,
    comptime A: type,
) OpCtorsType(F, A) {
    const OpCtorDefs = GetCtorDefs(F, A);
    const CtorEnum = std.meta.DeclEnum(OpCtorDefs);
    const enum_fields = std.meta.fields(CtorEnum);

    var op_ctors: [enum_fields.len]OpCtorInfo(A, CtorEnum, OpCtorDefs) = undefined;
    inline for (enum_fields, 0..) |field, i| {
        const name = field.name;
        const OpLam = @field(OpCtorDefs, name);
        const fn_info = @typeInfo(@TypeOf(OpLam.call));
        const params_len = fn_info.Fn.params.len;
        const ctor_e = @as(CtorEnum, @enumFromInt(i));
        op_ctors[i].ctor_e = ctor_e;
        // The call function of OpLam has a self parameter, all real parameters are not
        // include it.
        op_ctors[i].params_len = params_len - 1;
    }
    return op_ctors;
}

/// All value constructors for Maybe Functor
fn MaybeCtorDefs(comptime A: type) type {
    // Define Op constructor lambdas for StateF
    return struct {
        pub const Nothing = NothingLam;
        pub const Just = JustLam;

        const NothingLam = extern struct {
            lam_ctx: u64,

            const Self = @This();
            pub fn build() Self {
                return .{ .lam_ctx = 0 };
            }

            pub fn fpureToFreem(FreeMType: type, fpure: Maybe(A)) error{}!FreeMType {
                _ = fpure;
                const ops_array = [_]FOpInfo{
                    .{ .op_e = Nothing, .op_lam = @bitCast(try build()) },
                };
                return FreeMType.freeM(base.defaultVal(A), &ops_array);
            }

            pub fn deinit(self: Self) void {
                _ = self;
            }

            pub fn call(self: *const Self) Maybe(A) {
                _ = self;
                return null;
            }
        };

        const JustLam = extern struct {
            lam_ctx: u64,

            const Self = @This();
            pub fn build() Self {
                return .{ .lam_ctx = 0 };
            }

            pub fn fpureToFreem(FreeMType: type, fpure: Maybe(A)) error{}!FreeMType {
                const ops_array = [_]FOpInfo{
                    .{ .op_e = Just, .op_lam = @bitCast(try build()) },
                };
                const a = fpure.?;
                return FreeMType.freeM(a, &ops_array);
            }

            pub fn deinit(self: Self) void {
                _ = self;
            }

            pub fn call(self: *const Self, a: A) Maybe(A) {
                _ = self;
                return a;
            }
        };
    };
}

fn maybeToA(comptime A: type) *const fn (a: Maybe(A)) A {
    return struct {
        fn iterFn(a: Maybe(A)) A {
            return a orelse 0;
        }
    }.iterFn;
}

test "FreeMonad(F, A) constructor functions and iter" {
    const allocator = testing.allocator;
    const cfg = base.getDefaultBaseCfg(allocator);
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const maybe_functor = MaybeFunctor.init(.{ .none = {} });

    var a: u32 = 42;
    _ = &a;
    const pure_freem = FreeMonad(cfg, Maybe, u32).pureM(a);
    try testing.expectEqual(42, pure_freem.pure_m);

    const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
    const Nothing: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Nothing);
    const buildNothing = MaybeCtorDefs(u32).Nothing.build;
    const Just: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Just);
    const buildJust = MaybeCtorDefs(u32).Just.build;

    const just_fns = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildNothing()) },
    };
    var free_maybe = try FreeMonad(cfg, Maybe, u32).freeM(42, @constCast(just_fns));
    try testing.expectEqual(42, try free_maybe.iter(maybe_functor, maybeToA(u32)));

    free_maybe = try free_maybe.appendFOp(.{ .op_e = Just, .op_lam = @bitCast(buildJust()) });
    try testing.expectEqual(42, try free_maybe.iter(maybe_functor, maybeToA(u32)));

    const just_fns3 = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
        .{ .op_e = Nothing, .op_lam = @bitCast(buildNothing()) },
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };
    free_maybe = try free_maybe.appendFOps(@constCast(just_fns3));
    defer free_maybe.deinit();
    try testing.expectEqual(0, try free_maybe.iter(maybe_functor, maybeToA(u32)));
}

const MWriterMaybe = state.MWriterMaybe;

pub const MaybeShowNatImpl = struct {
    allocator: Allocator,

    const Self = @This();

    pub const F = Maybe;
    pub const G = MWriterMaybe(ArrayList(u8));
    pub const Error = Allocator.Error;

    pub fn trans(self: Self, comptime A: type, fa: F(A)) Error!G(A) {
        if (fa) |a| {
            const just_str = "Just ";
            var array = try ArrayList(u8).initCapacity(self.allocator, just_str.len);
            array.appendSliceAssumeCapacity(just_str);
            return .{ .a = a, .w = array };
        } else {
            // return empty ArrayList
            const array = ArrayList(u8).init(self.allocator);
            return .{ .a = @as(Maybe(A), null), .w = array };
        }
    }
};

const MaybeToArrayListNatImpl = functor.MaybeToArrayListNatImpl;
const MWriterMaybeMonadImpl = state.MWriterMaybeMonadImpl;

pub fn ArrayListMonoidImpl(comptime T: type) type {
    return struct {
        allocator: Allocator,

        const Self = @This();
        pub const M = ArrayList(T);
        pub const Error = Allocator.Error;

        pub fn mempty(self: Self) Error!M {
            return ArrayList(T).init(self.allocator);
        }

        pub fn mappend(self: Self, ma: M, mb: M) Error!M {
            _ = self;
            var mc = try ArrayList(T).initCapacity(ma.allocator, ma.items.len + mb.items.len);
            mc.appendSliceAssumeCapacity(ma.items);
            mc.appendSliceAssumeCapacity(mb.items);
            return mc;
        }
    };
}

test "FreeMonad(F, A) constructor functions and foldFree" {
    const allocator = testing.allocator;
    const cfg = base.getDefaultBaseCfg(allocator);
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const maybe_functor = MaybeFunctor.init(.{ .none = {} });
    const ArrayListMonad = Monad(ArrayListMonadImpl);
    const array_monad = ArrayListMonad.init(.{ .allocator = allocator });
    const NatMaybeToArray = NatTrans(MaybeToArrayListNatImpl);
    const nat_maybe_array = NatMaybeToArray.init(.{ .instanceArray = .{ .allocator = allocator } });

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatMaybeToShow = NatTrans(MaybeShowNatImpl);
    const nat_maybe_show = NatMaybeToShow.init(.{ .allocator = allocator });

    var a: u32 = 42;
    _ = &a;

    const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
    const Nothing: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Nothing);
    const buildNothing = MaybeCtorDefs(u32).Nothing.build;
    const Just: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Just);
    const buildJust = MaybeCtorDefs(u32).Just.build;
    const just_fns = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };
    var free_maybe = try FreeMonad(cfg, Maybe, u32).freeM(42, @constCast(just_fns));
    defer free_maybe.deinit();

    const folded = try free_maybe.foldFree(nat_maybe_array, maybe_functor, array_monad);
    defer folded.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{42}, folded.items);
    const show_writer = try free_maybe.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show_writer.deinit();
    try testing.expectEqual(42, show_writer.a);
    try testing.expectEqualSlices(u8, "Just ", show_writer.w.items);

    free_maybe = try free_maybe.appendFOp(.{ .op_e = Just, .op_lam = @bitCast(buildJust()) });
    const folded1 = try free_maybe.foldFree(nat_maybe_array, maybe_functor, array_monad);
    defer folded1.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{42}, folded1.items);
    const show1_writer = try free_maybe.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show1_writer.deinit();
    try testing.expectEqual(42, show1_writer.a);
    try testing.expectEqualSlices(u8, "Just Just ", show1_writer.w.items);

    const just_fns3 = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
        .{ .op_e = Nothing, .op_lam = @bitCast(buildNothing()) },
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };
    free_maybe = try free_maybe.appendFOps(@constCast(just_fns3));
    const folded2 = try free_maybe.foldFree(nat_maybe_array, maybe_functor, array_monad);
    defer folded2.deinit();
    try testing.expectEqualSlices(u32, &[_]u32{}, folded2.items);
    const show2_writer = try free_maybe.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show2_writer.deinit();
    try testing.expectEqual(null, show2_writer.a);
    try testing.expectEqualSlices(u8, "Just ", show2_writer.w.items);
}

pub fn liftNothing(comptime cfg: anytype, comptime A: type) !FreeMonad(cfg, Maybe, A) {
    const CtorEnum = std.meta.DeclEnum(MaybeCtorDefs(A));
    const Nothing: FOpEnumInt = @intFromEnum(CtorEnum.Nothing);
    const buildNothing = MaybeCtorDefs(A).Nothing.build;
    const ops_array = &[_]FOpInfo{
        .{ .op_e = Nothing, .op_lam = @bitCast(buildNothing()) },
    };

    const a = base.defaultVal(A);
    return FreeMonad(cfg, Maybe, A).freeM(a, @constCast(ops_array));
}

pub fn liftJust(comptime cfg: anytype, a: anytype) !FreeMonad(cfg, Maybe, @TypeOf(a)) {
    const A = @TypeOf(a);
    const CtorEnum = std.meta.DeclEnum(MaybeCtorDefs(A));
    const Just: FOpEnumInt = @intFromEnum(CtorEnum.Just);
    const buildJust = MaybeCtorDefs(A).Just.build;
    const ops_array = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };

    return FreeMonad(cfg, Maybe, A).freeM(a, @constCast(ops_array));
}

test "FreeMonad(Maybe, A) liftNothing and liftJust" {
    const allocator = testing.allocator;
    const cfg = base.getDefaultBaseCfg(allocator);
    const MaybeFunctor = Functor(MaybeMonadImpl);
    var maybe_functor = MaybeFunctor.init(.{ .none = {} });
    _ = &maybe_functor;

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatMaybeToShow = NatTrans(MaybeShowNatImpl);
    const nat_maybe_show = NatMaybeToShow.init(.{ .allocator = allocator });

    const a: u32 = 42;
    const just1 = try liftJust(cfg, a);
    defer just1.deinit();
    const show1_writer = try just1.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show1_writer.deinit();
    try testing.expectEqual(42, show1_writer.a);
    try testing.expectEqualSlices(u8, "Just ", show1_writer.w.items);

    const nothing1 = try liftNothing(cfg, u32);
    defer nothing1.deinit();
    const show3_writer = try nothing1.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show3_writer.deinit();
    try testing.expectEqual(null, show3_writer.a);
    try testing.expectEqualSlices(u8, "", show3_writer.w.items);
}

/// The Monad instance of FreeMonad, the parameter FunF is a Functor.
pub fn FreeMonadImpl(
    comptime cfg: anytype,
    comptime FunF: TCtor,
    comptime FunFImpl: type,
) type {
    return struct {
        allocator: Allocator,
        funf_impl: FunFImpl,

        const Self = @This();

        /// Constructor Type for Functor, Applicative, Monad, ...
        pub const F = FreeM(cfg, FunF);

        /// Get base type of FreeMonad(F, A), it is must just is A.
        pub fn BaseType(comptime FreeFA: type) type {
            return FreeFA.BaseType;
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
                return free_fn(fa.pure_m);
            }
            if (fa == .free_m and fa.free_m[0].* == .pure_m) {
                free_fn(fa.free_m[0].pure_m);
            }
            fa.deinit();
        }

        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            const A = MapFnInType(@TypeOf(map_fn));
            const B = MapFnRetType(@TypeOf(map_fn));
            const has_err, const _B = comptime isErrorUnionOrVal(B);

            const is_only_fop, const free_fop = if (comptime isMapRef(K)) blk_t: {
                break :blk_t if (fa.* == .free_fop)
                    .{ true, &fa.free_fop }
                else if (fa.* == .free_m and fa.free_m[0].* == .free_fop)
                    .{ false, &fa.free_m[0].free_fop }
                else
                    .{ false, null };
            } else blk_f: {
                break :blk_f if (fa == .free_fop)
                    .{ true, fa.free_fop }
                else if (fa == .free_m and fa.free_m[0].* == .free_fop)
                    .{ false, fa.free_m[0].free_fop }
                else
                    .{ false, null };
            };

            if (free_fop) |_free_fop| {
                const inner_map_lam = struct {
                    fimpl: *Self,
                    map_fn: *const fn (A) B,

                    const SelfMap = @This();
                    pub fn call(
                        self_map: *const SelfMap,
                        freem: FaType(K, @TypeOf(map_fn)),
                    ) FbType(@TypeOf(map_fn)) {
                        defer {
                            if (isInplaceMap(K)) {
                                if (freem == .free_m) {
                                    // free the pure value in temporary freem that
                                    // generated by x_to_freem
                                    freem.free_m[0].deinit();
                                    freem.free_m[1].allocator.destroy(freem.free_m[0]);
                                }
                            } else freem.deinit();
                        }
                        // recusive call fmap for inner free monad
                        return self_map.fimpl.fmap(K, self_map.map_fn, freem);
                    }
                }{ .fimpl = self, .map_fn = map_fn };

                const x_to_freem = if (isInplaceMap(K)) _free_fop[0] else _free_fop[0].strongRef();
                const new_op_info = if (isInplaceMap(K))
                    _free_fop[1]
                else
                    try @TypeOf(fa).copyOrCloneFOp(_free_fop[1]);
                const new_x_to_freem = try x_to_freem.appendLam(inner_map_lam);
                if (is_only_fop) {
                    return .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                } else {
                    if (isInplaceMap(K)) {
                        // reuse the allocated memory of free_m[0] in fa,
                        var new_freem: *FreeMonad(cfg, FunF, _B) = @ptrCast(fa.free_m[0]);
                        new_freem.free_fop = .{ new_x_to_freem, new_op_info };
                        return .{ .free_m = .{ new_freem, fa.free_m[1] } };
                    } else {
                        const new_freem = try self.allocator.create(FreeMonad(cfg, FunF, _B));
                        new_freem.* = .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                        return .{ .free_m = .{ new_freem, try fa.cloneFOps() } };
                    }
                }
            }

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
                const new_pure_m = try self.allocator.create(FreeMonad(cfg, FunF, _B));
                new_pure_m.* = .{ .pure_m = _b };
                if (isInplaceMap(K)) {
                    return .{ .free_m = .{ new_pure_m, fa.free_m[1] } };
                } else {
                    return .{ .free_m = .{ new_pure_m, try fa.cloneFOps() } };
                }
            }
        }

        pub fn fmapLam(
            self: *const Self,
            comptime K: MapFnKind,
            map_lam: anytype,
            fa: FaLamType(K, @TypeOf(map_lam)),
        ) FbLamType(@TypeOf(map_lam)) {
            const B = MapLamRetType(@TypeOf(map_lam));
            const has_err, const _B = comptime isErrorUnionOrVal(B);

            const is_only_fop, const free_fop = if (comptime isMapRef(K)) blk_t: {
                break :blk_t if (fa.* == .free_fop)
                    .{ true, fa.free_fop }
                else if (fa.* == .free_m and fa.free_m[0].* == .free_fop)
                    .{ false, fa.free_m[0].free_fop }
                else
                    .{ false, null };
            } else blk_f: {
                break :blk_f if (fa == .free_fop)
                    .{ true, fa.free_fop }
                else if (fa == .free_m and fa.free_m[0].* == .free_fop)
                    .{ false, fa.free_m[0].free_fop }
                else
                    .{ false, null };
            };

            if (free_fop) |_free_fop| {
                const inner_map_lam = struct {
                    fimpl: *const Self,
                    map_lam: @TypeOf(map_lam),

                    const SelfMap = @This();
                    pub fn deinit(self_map: SelfMap) void {
                        base.deinitOrUnref(self_map.map_lam);
                    }

                    pub fn call(
                        self_map: *const SelfMap,
                        freem: FaLamType(K, @TypeOf(map_lam)),
                    ) FbLamType(@TypeOf(map_lam)) {
                        defer {
                            if (isInplaceMap(K)) {
                                if (freem == .free_m) {
                                    // free the pure value in temporary freem that
                                    // generated by x_to_freem
                                    freem.free_m[0].deinit();
                                    freem.free_m[1].allocator.destroy(freem.free_m[0]);
                                }
                            } else freem.deinit();
                        }
                        // recusive call fmapLam for inner free monad
                        return self_map.fimpl.fmapLam(K, self_map.map_lam, freem);
                    }
                }{ .fimpl = self, .map_lam = try base.copyOrCloneOrRef(map_lam) };

                const x_to_freem = if (isInplaceMap(K)) _free_fop[0] else _free_fop[0].strongRef();
                const new_op_info = if (isInplaceMap(K))
                    _free_fop[1]
                else
                    try @TypeOf(fa).copyOrCloneFOp(_free_fop[1]);
                const new_x_to_freem = try x_to_freem.appendLam(inner_map_lam);
                if (is_only_fop) {
                    return .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                } else {
                    if (isInplaceMap(K)) {
                        // reuse the allocated memory of free_m[0] in fa,
                        var new_freem: *FreeMonad(cfg, FunF, _B) = @ptrCast(fa.free_m[0]);
                        new_freem.free_fop = .{ new_x_to_freem, new_op_info };
                        return .{ .free_m = .{ new_freem, fa.free_m[1] } };
                    } else {
                        const new_freem = try self.allocator.create(FreeMonad(cfg, FunF, _B));
                        new_freem.* = .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                        return .{ .free_m = .{ new_freem, try fa.cloneFOps() } };
                    }
                }
            }

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
                const new_pure_m = try self.allocator.create(FreeMonad(cfg, FunF, _B));
                new_pure_m.* = .{ .pure_m = _b };
                if (isInplaceMap(K)) {
                    return .{ .free_m = .{ new_pure_m, fa.free_m[1] } };
                } else {
                    return .{ .free_m = .{ new_pure_m, try fa.cloneFOps() } };
                }
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

            const is_only_fop, const free_fop = blk: {
                break :blk if (ff == .free_fop)
                    .{ true, ff.free_fop }
                else if (ff == .free_m and ff.free_m[0].* == .free_fop)
                    .{ false, ff.free_m[0].free_fop }
                else
                    .{ false, null };
            };

            if (free_fop) |_free_fop| {
                const inner_apply_lam = struct {
                    fimpl: *Self,
                    local_fa: F(A),

                    const SelfApply = @This();
                    pub fn deinit(self_apply: SelfApply) void {
                        base.tryStrongUnref(self_apply.local_fa);
                    }

                    pub fn call(
                        self_apply: *const SelfApply,
                        freem: F(*const fn (A) B),
                    ) AFbType(B) {
                        defer {
                            freem.deinit();
                        }
                        // recusive call fapply for inner free monad
                        return self_apply.fimpl.fapply(A, B, freem, self_apply.local_fa);
                    }
                }{ .fimpl = self, .local_fa = try base.copyOrCloneOrRef(fa) };

                const x_to_freem = _free_fop[0].strongRef();
                const new_op_info = try @TypeOf(ff).copyOrCloneFOp(_free_fop[1]);
                const new_x_to_freem = try x_to_freem.appendLam(inner_apply_lam);
                if (is_only_fop) {
                    return .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                } else {
                    const new_freem = try self.allocator.create(FreeMonad(cfg, FunF, _B));
                    new_freem.* = .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                    return .{ .free_m = .{ new_freem, try ff.cloneFOps() } };
                }
            }

            const map_fn = ff.free_m[0].pure_m;
            if (fa == .pure_m) {
                const b = map_fn(fa.pure_m);
                const _b = if (has_err) try b else b;
                const new_pure_m = try self.allocator.create(F(_B));
                new_pure_m.* = .{ .pure_m = _b };
                return .{ .free_m = .{ new_pure_m, try ff.cloneFOps() } };
            } else if (fa == .free_fop) {
                const fb = try self.fmap(.NewValMap, map_fn, fa);
                const new_pure_m = try self.allocator.create(F(_B));
                new_pure_m.* = .{ .free_fop = fb.free_fop };
                return .{ .free_m = .{ new_pure_m, try ff.cloneFOps() } };
            } else {
                const part_fb = try self.fmap(.NewValMap, map_fn, fa);
                const new_pure_m = part_fb.free_m[0];
                var flist = part_fb.free_m[1];
                const new_ff_fops = try flist.addManyAsSlice(ff.free_m[1].items.len);
                try ff.cloneFOpsToSlice(new_ff_fops);
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
                return try self.fmapLam(.NewValMap, flam.pure_m, fa);
            }

            const is_only_fop, const free_fop = blk: {
                break :blk if (flam == .free_fop)
                    .{ true, flam.free_fop }
                else if (flam == .free_m and flam.free_m[0].* == .free_fop)
                    .{ false, flam.free_m[0].free_fop }
                else
                    .{ false, null };
            };

            if (free_fop) |_free_fop| {
                const inner_apply_lam = struct {
                    fimpl: *Self,
                    local_fa: F(A),

                    const SelfApply = @This();
                    pub fn deinit(self_apply: SelfApply) void {
                        base.tryStrongUnref(self_apply.local_fa);
                    }

                    pub fn call(
                        self_apply: *const SelfApply,
                        freem: @TypeOf(flam),
                    ) AFbType(B) {
                        defer {
                            freem.deinit();
                        }
                        // recusive call fapplyLam for inner free monad
                        return self_apply.fimpl.fapplyLam(A, B, freem, self_apply.local_fa);
                    }
                }{ .fimpl = self, .local_fa = try base.copyOrCloneOrRef(fa) };

                const x_to_freem = _free_fop[0].strongRef();
                const new_op_info = try @TypeOf(flam).copyOrCloneFOp(_free_fop[1]);
                const new_x_to_freem = try x_to_freem.appendLam(inner_apply_lam);
                if (is_only_fop) {
                    return .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                } else {
                    const new_freem = try self.allocator.create(FreeMonad(cfg, FunF, _B));
                    new_freem.* = .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                    return .{ .free_m = .{ new_freem, try flam.cloneFOps() } };
                }
            }

            const map_lam = flam.free_m[0].pure_m;
            if (fa == .pure_m) {
                const b = map_lam.call(fa.pure_m);
                const _b = if (has_err) try b else b;
                const new_pure_m = try self.allocator.create(F(_B));
                new_pure_m.* = .{ .pure_m = _b };
                return .{ .free_m = .{ new_pure_m, try flam.free_m[1].clone() } };
            } else if (fa == .free_fop) {
                const fb = try self.fmapLam(.NewValMap, map_lam, fa);
                const new_pure_m = try self.allocator.create(F(_B));
                new_pure_m.* = .{ .free_fop = fb.free_fop };
                return .{ .free_m = .{ new_pure_m, try flam.cloneFOps() } };
            } else {
                const part_fb = try self.fmapLam(.NewValMap, map_lam, fa);
                const new_pure_m = part_fb.free_m[0];
                var flist = part_fb.free_m[1];
                const new_ff_fops = try flist.addManyAsSlice(flam.free_m[1].items.len);
                try flam.cloneFOpsToSlice(new_ff_fops);
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
                return try k(self, ma.pure_m);
            }

            const is_only_fop, const free_fop = blk: {
                break :blk if (ma == .free_fop)
                    .{ true, ma.free_fop }
                else if (ma == .free_m and ma.free_m[0].* == .free_fop)
                    .{ false, ma.free_m[0].free_fop }
                else
                    .{ false, null };
            };

            if (free_fop) |_free_fop| {
                const inner_bind_lam = struct {
                    fimpl: *Self,
                    local_k: @TypeOf(k),

                    const SelfBind = @This();
                    pub fn call(
                        self_bind: *const SelfBind,
                        freem: @TypeOf(ma),
                    ) MbType(B) {
                        defer {
                            freem.deinit();
                        }
                        // recusive call bind for inner free monad
                        return self_bind.fimpl.bind(A, B, freem, self_bind.local_k);
                    }
                }{ .fimpl = self, .local_k = k };

                const x_to_freem = _free_fop[0].strongRef();
                const new_op_info = try @TypeOf(ma).copyOrCloneFOp(_free_fop[1]);
                const new_x_to_freem = try x_to_freem.appendLam(inner_bind_lam);
                if (is_only_fop) {
                    return .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                } else {
                    const new_freem = try self.allocator.create(FreeMonad(cfg, FunF, B));
                    new_freem.* = .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                    return .{ .free_m = .{ new_freem, try ma.cloneFOps() } };
                }
            }

            const freem = try k(self, ma.free_m[0].pure_m);
            if (freem == .pure_m) {
                const new_pure_m = try self.allocator.create(F(B));
                new_pure_m.* = .{ .pure_m = freem.pure_m };
                return .{ .free_m = .{ new_pure_m, try ma.cloneFOps() } };
            } else if (freem == .free_fop) {
                const new_pure_m = try self.allocator.create(F(B));
                new_pure_m.* = .{ .free_fop = freem.free_fop };
                return .{ .free_m = .{ new_pure_m, try ma.cloneFOps() } };
            } else {
                var flist = freem.free_m[1];
                const new_ma_fops = try flist.addManyAsSlice(ma.free_m[1].items.len);
                try ma.cloneFOpsToSlice(new_ma_fops);
                return .{ .free_m = .{ freem.free_m[0], flist } };
            }
        }

        pub fn join(
            self: *Self,
            comptime A: type,
            mma: F(F(A)),
        ) MbType(A) {
            if (mma == .pure_m) {
                return mma.pure_m;
            }

            const is_only_fop, const free_fop = blk: {
                break :blk if (mma == .free_fop)
                    .{ true, mma.free_fop }
                else if (mma == .free_m and mma.free_m[0].* == .free_fop)
                    .{ false, mma.free_m[0].free_fop }
                else
                    .{ false, null };
            };

            if (free_fop) |_free_fop| {
                const inner_bind_lam = struct {
                    fimpl: *Self,

                    const SelfBind = @This();
                    pub fn call(
                        self_bind: *const SelfBind,
                        freem: @TypeOf(mma),
                    ) MbType(A) {
                        defer freem.deinit();
                        // recusive call join for inner free monad
                        return self_bind.fimpl.join(A, freem);
                    }
                }{ .fimpl = self };

                const x_to_freem = _free_fop[0].strongRef();
                const new_op_info = try @TypeOf(mma).copyOrCloneFOp(_free_fop[1]);
                const new_x_to_freem = try x_to_freem.appendLam(inner_bind_lam);
                if (is_only_fop) {
                    return .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                } else {
                    // TODO: In InplaceMap mode, reuse the allocated memory of free_m[0]
                    // in mma,
                    // const new_freem: *FreeMonad(FunF, A) = @ptrCast(mma.free_m[0]);
                    const new_freem = try self.allocator.create(F(A));
                    new_freem.* = .{ .free_fop = .{ new_x_to_freem, new_op_info } };
                    return .{ .free_m = .{ new_freem, try mma.cloneFOps() } };
                }
            }

            // mma.free_m[0].pure is a FreeMonad(F, A).
            const freem = mma.free_m[0].pure_m;
            if (freem == .pure_m) {
                const new_pure_m = try self.allocator.create(F(A));
                new_pure_m.* = .{ .pure_m = freem.pure_m };
                return .{ .free_m = .{ new_pure_m, try mma.cloneFOps() } };
            } else if (freem == .free_fop) {
                const new_pure_m = try self.allocator.create(F(A));
                new_pure_m.* = .{ .free_fop = freem.free_fop };
                return .{ .free_m = .{ new_pure_m, try mma.cloneFOps() } };
            } else {
                var flist = freem.free_m[1];
                const outter_fops = try flist.addManyAsSlice(mma.free_m[1].items.len);
                try mma.cloneFOpsToSlice(outter_fops);
                return .{ .free_m = .{ freem.free_m[0], flist } };
            }
        }
    };
}

// These functions are defined for unit test
const add10 = testu.add10;
const add_pi_f64 = &testu.add_pi_f64;
const mul_pi_f64 = &testu.mul_pi_f64;

const Add_x_u32_Lam = testu.Add_x_u32_Lam;
const Add_x_f64_Lam = testu.Add_x_f64_Lam;

test "FreeMonad(F, A) fmap" {
    const allocator = testing.allocator;
    const cfg = base.getDefaultBaseCfg(allocator);
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const maybe_functor = MaybeFunctor.init(.{ .none = {} });
    const FreeMFunctor = Functor(FreeMonadImpl(cfg, Maybe, MaybeMonadImpl));
    var freem_functor = FreeMFunctor.init(.{
        .allocator = allocator,
        .funf_impl = maybe_functor,
    });

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatMaybeToShow = NatTrans(MaybeShowNatImpl);
    const nat_maybe_show = NatMaybeToShow.init(.{ .allocator = allocator });

    var a: u32 = 42;
    _ = &a;
    // const pure_freem = .{ .pure_m = a };
    const pure_freem = FreeMonad(cfg, Maybe, u32).pureM(@as(u32, 42));
    const pure_freem1 = try freem_functor.fmap(.NewValMap, add_pi_f64, pure_freem);
    try testing.expectEqual(45.14, try pure_freem1.iter(maybe_functor, maybeToA(f64)));
    const show_writer = try pure_freem1.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show_writer.deinit();
    try testing.expectEqual(45.14, show_writer.a);
    try testing.expectEqualSlices(u8, "", show_writer.w.items);

    const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
    const Just: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Just);
    const buildJust = MaybeCtorDefs(u32).Just.build;
    // const Nothing: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Nothing);
    const just_fns2 = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };
    const free_maybe = try pure_freem.appendFOps(@constCast(just_fns2));
    defer free_maybe.deinit();
    const free_maybe1 = try freem_functor.fmap(.NewValMap, add10, free_maybe);
    defer free_maybe1.deinit();
    try testing.expectEqual(52, try free_maybe1.iter(maybe_functor, maybeToA(u32)));
    const show1_writer = try free_maybe1.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show1_writer.deinit();
    try testing.expectEqual(52, show1_writer.a);
    try testing.expectEqualSlices(u8, "Just Just ", show1_writer.w.items);

    const add_x_f64_lam = Add_x_f64_Lam{ ._x = 3.14 };
    const free_maybe2 = try freem_functor.fmapLam(.NewValMap, add_x_f64_lam, free_maybe1);
    defer free_maybe2.deinit();
    try testing.expectEqual(55.14, try free_maybe2.iter(maybe_functor, maybeToA(f64)));
    const show2_writer = try free_maybe2.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show2_writer.deinit();
    try testing.expectEqual(55.14, show2_writer.a);
    try testing.expectEqualSlices(u8, "Just Just ", show2_writer.w.items);
}

test "FreeMonad(F, A) pure and fapply" {
    const allocator = testing.allocator;
    const cfg = base.getDefaultBaseCfg(allocator);
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const maybe_functor = MaybeFunctor.init(.{ .none = {} });
    const FreeMApplicative = Applicative(FreeMonadImpl(cfg, Maybe, MaybeMonadImpl));
    var freem_applicative = FreeMApplicative.init(.{
        .allocator = allocator,
        .funf_impl = maybe_functor,
    });

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatMaybeToShow = NatTrans(MaybeShowNatImpl);
    const nat_maybe_show = NatMaybeToShow.init(.{ .allocator = allocator });

    var a: u32 = 42;
    _ = &a;
    const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
    const Nothing: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Nothing);
    const buildNothing = MaybeCtorDefs(u32).Nothing.build;
    const Just: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Just);
    const buildJust = MaybeCtorDefs(u32).Just.build;
    const just_fns1 = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };

    const pure_freem = FreeMonad(cfg, Maybe, u32).pureM(@as(u32, 33));
    const purem_fn = try freem_applicative.pure(add_pi_f64);
    var freem_fn = try purem_fn.appendFOp(.{ .op_e = Just, .op_lam = @bitCast(buildJust()) });
    defer freem_fn.deinit();
    const applied_purem = try freem_applicative.fapply(u32, f64, freem_fn, pure_freem);
    defer applied_purem.deinit();
    try testing.expectEqual(36.14, try applied_purem.iter(maybe_functor, maybeToA(f64)));
    const show_writer = try applied_purem.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show_writer.deinit();
    try testing.expectEqual(36.14, show_writer.a);
    try testing.expectEqualSlices(u8, "Just ", show_writer.w.items);

    const freem_a = try FreeMonad(cfg, Maybe, u32).freeM(42, @constCast(just_fns1));
    defer freem_a.deinit();
    const applied_freem = try freem_applicative.fapply(u32, f64, freem_fn, freem_a);
    defer applied_freem.deinit();
    try testing.expectEqual(45.14, try applied_freem.iter(maybe_functor, maybeToA(f64)));
    const show1_writer = try applied_freem.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show1_writer.deinit();
    try testing.expectEqual(45.14, show1_writer.a);
    try testing.expectEqualSlices(u8, "Just Just Just ", show1_writer.w.items);

    const applied_purem1 = try freem_applicative.fapply(u32, f64, purem_fn, freem_a);
    defer applied_purem1.deinit();
    try testing.expectEqual(45.14, try applied_purem1.iter(maybe_functor, maybeToA(f64)));
    const show1_purem = try applied_purem1.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show1_purem.deinit();
    try testing.expectEqual(45.14, show1_purem.a);
    try testing.expectEqualSlices(u8, "Just Just ", show1_purem.w.items);

    const add_x_f64_lam = Add_x_f64_Lam{ ._x = 3.14 };
    var freem_lam = try freem_applicative.pure(add_x_f64_lam);
    defer freem_lam.deinit();
    const just_fns2 = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
        .{ .op_e = Nothing, .op_lam = @bitCast(buildNothing()) },
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };
    freem_lam = try freem_lam.appendFOps(@constCast(just_fns2));
    const applied_freem1 = try freem_applicative.fapplyLam(u32, f64, freem_lam, freem_a);
    defer applied_freem1.deinit();
    try testing.expectEqual(0, try applied_freem1.iter(maybe_functor, maybeToA(f64)));
    const show2_writer = try applied_freem1.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show2_writer.deinit();
    try testing.expectEqual(null, show2_writer.a);
    try testing.expectEqualSlices(u8, "Just ", show2_writer.w.items);
}

test "FreeMonad(F, A) bind" {
    const allocator = testing.allocator;
    const cfg = base.getDefaultBaseCfg(allocator);
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const maybe_functor = MaybeFunctor.init(.{ .none = {} });
    const FreeMaybeImpl = FreeMonadImpl(cfg, Maybe, MaybeMonadImpl);
    const FMaybeMonad = Monad(FreeMaybeImpl);
    var freem_monad = FMaybeMonad.init(.{
        .allocator = allocator,
        .funf_impl = maybe_functor,
    });

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatMaybeToShow = NatTrans(MaybeShowNatImpl);
    const nat_maybe_show = NatMaybeToShow.init(.{ .allocator = allocator });

    const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
    const Nothing: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Nothing);
    const buildNothing = MaybeCtorDefs(u32).Nothing.build;
    const Just: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Just);
    const buildJust = MaybeCtorDefs(u32).Just.build;
    const just_fns1 = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };

    const pure_freem = FreeMonad(cfg, Maybe, u32).pureM(@as(u32, 1));
    const freem_a = try FreeMonad(cfg, Maybe, u32).freeM(2, @constCast(just_fns1));
    defer freem_a.deinit();
    const freem_b = try FreeMonad(cfg, Maybe, u32).freeM(3, @constCast(just_fns1));
    defer freem_b.deinit();
    const freem_c = try FreeMonad(cfg, Maybe, u32).freeM(8, @constCast(just_fns1));
    defer freem_c.deinit();

    const k_u32 = struct {
        fn f(self: *FreeMaybeImpl, a: u32) !FreeMonad(cfg, Maybe, f64) {
            const _a = if (a > 3) 0 else a;
            const just_array = switch (_a) {
                0 => &[_]FOpInfo{},
                1 => &[_]FOpInfo{
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                },
                2 => &[_]FOpInfo{
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                },
                3 => &[_]FOpInfo{
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                    .{ .op_e = Nothing, .op_lam = @bitCast(buildNothing()) },
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                },
                else => @panic("The _a is not greater than 3"),
            };
            const b = @as(f64, @floatFromInt(a)) + 3.14;

            const freem_k = if (just_array.len > 0)
                try FreeMonad(cfg, Maybe, f64).freeM(b, @constCast(just_array))
            else
                try self.pure(b);
            return freem_k;
        }
    }.f;

    const purem_binded = try freem_monad.bind(u32, f64, pure_freem, k_u32);
    defer purem_binded.deinit();
    const show_writer = try purem_binded.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show_writer.deinit();
    try testing.expectApproxEqRel(4.14, show_writer.a.?, std.math.floatEps(f64));
    try testing.expectEqualSlices(u8, "Just ", show_writer.w.items);

    const freem_binded = try freem_monad.bind(u32, f64, freem_a, k_u32);
    defer freem_binded.deinit();
    const show1_writer = try freem_binded.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show1_writer.deinit();
    try testing.expectApproxEqRel(5.14, show1_writer.a.?, std.math.floatEps(f64));
    try testing.expectEqualSlices(u8, "Just Just Just Just ", show1_writer.w.items);

    const freem_binded2 = try freem_monad.bind(u32, f64, freem_b, k_u32);
    defer freem_binded2.deinit();
    try testing.expectEqual(0, try freem_binded2.iter(maybe_functor, maybeToA(f64)));
    const show2_writer = try freem_binded2.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show2_writer.deinit();
    try testing.expectEqual(null, show2_writer.a);
    try testing.expectEqualSlices(u8, "Just Just Just ", show2_writer.w.items);

    const freem_binded3 = try freem_monad.bind(u32, f64, freem_c, k_u32);
    defer freem_binded3.deinit();
    const show3_writer = try freem_binded3.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show3_writer.deinit();
    try testing.expectApproxEqRel(11.14, show3_writer.a.?, std.math.floatEps(f64));
    try testing.expectEqualSlices(u8, "Just Just ", show3_writer.w.items);
}

test "FreeMonad(F, A) join" {
    const allocator = testing.allocator;
    const cfg = base.getDefaultBaseCfg(allocator);
    const MaybeFunctor = Functor(MaybeMonadImpl);
    const maybe_functor = MaybeFunctor.init(.{ .none = {} });
    const FreeMaybeImpl = FreeMonadImpl(cfg, Maybe, MaybeMonadImpl);
    const FMaybeMonad = Monad(FreeMaybeImpl);
    var freem_monad = FMaybeMonad.init(.{
        .allocator = allocator,
        .funf_impl = maybe_functor,
    });

    const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
    const ShowMonad = Monad(ShowMonadImpl);
    const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
    const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
    const NatMaybeToShow = NatTrans(MaybeShowNatImpl);
    const nat_maybe_show = NatMaybeToShow.init(.{ .allocator = allocator });

    const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
    const Nothing: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Nothing);
    const buildNothing = MaybeCtorDefs(u32).Nothing.build;
    const Just: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Just);
    const buildJust = MaybeCtorDefs(u32).Just.build;
    const just_fns1 = &[_]FOpInfo{
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
        .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
    };

    const pure_freem = FreeMonad(cfg, Maybe, u32).pureM(@as(u32, 1));
    const freem_a = try FreeMonad(cfg, Maybe, u32).freeM(2, @constCast(just_fns1));
    defer freem_a.deinit();
    const freem_b = try FreeMonad(cfg, Maybe, u32).freeM(3, @constCast(just_fns1));
    defer freem_b.deinit();
    const freem_c = try FreeMonad(cfg, Maybe, u32).freeM(8, @constCast(just_fns1));
    defer freem_c.deinit();

    const k_u32 = struct {
        allocator: Allocator,

        const Self = @This();
        pub fn call(self: *const Self, a: u32) !FreeMonad(cfg, Maybe, f64) {
            _ = self;
            const _a = if (a > 3) 0 else a;
            const just_array = switch (_a) {
                0 => &[_]FOpInfo{},
                1 => &[_]FOpInfo{
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                },
                2 => &[_]FOpInfo{
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                },
                3 => &[_]FOpInfo{
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                    .{ .op_e = Nothing, .op_lam = @bitCast(buildNothing()) },
                    .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
                },
                else => @panic("The _a is not greater than 3"),
            };
            const b = @as(f64, @floatFromInt(a)) + 3.14;

            const freem_k = if (just_array.len > 0)
                try FreeMonad(cfg, Maybe, f64).freeM(b, @constCast(just_array))
            else
                FreeMonad(cfg, Maybe, f64).pureM(b);
            return freem_k;
        }
    }{ .allocator = allocator };

    const pure_mma = try freem_monad.fmapLam(.NewValMap, k_u32, pure_freem);
    defer pure_mma.deinit();
    const purem_joined = try freem_monad.join(f64, pure_mma);
    defer purem_joined.deinit();
    const show_writer = try purem_joined.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show_writer.deinit();
    try testing.expectApproxEqRel(4.14, show_writer.a.?, std.math.floatEps(f64));
    try testing.expectEqualSlices(u8, "Just ", show_writer.w.items);

    const impure_mma = try freem_monad.fmapLam(.NewValMap, k_u32, freem_a);
    defer impure_mma.deinit();
    const freem_joined = try freem_monad.join(f64, impure_mma);
    defer freem_joined.deinit();
    const show1_writer = try freem_joined.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show1_writer.deinit();
    try testing.expectApproxEqRel(5.14, show1_writer.a.?, std.math.floatEps(f64));
    try testing.expectEqualSlices(u8, "Just Just Just Just ", show1_writer.w.items);

    const impure_mma2 = try freem_monad.fmapLam(.NewValMap, k_u32, freem_b);
    defer impure_mma2.deinit();
    const freem_joined2 = try freem_monad.join(f64, impure_mma2);
    defer freem_joined2.deinit();
    try testing.expectEqual(0, try freem_joined2.iter(maybe_functor, maybeToA(f64)));
    const show2_writer = try freem_joined2.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show2_writer.deinit();
    try testing.expectEqual(null, show2_writer.a);
    try testing.expectEqualSlices(u8, "Just Just Just ", show2_writer.w.items);

    const impure_mma3 = try freem_monad.fmapLam(.NewValMap, k_u32, freem_c);
    defer impure_mma3.deinit();
    const freem_joined3 = try freem_monad.join(f64, impure_mma3);
    defer freem_joined3.deinit();
    const show3_writer = try freem_joined3.foldFree(nat_maybe_show, maybe_functor, show_monad);
    defer show3_writer.deinit();
    try testing.expectApproxEqRel(11.14, show3_writer.a.?, std.math.floatEps(f64));
    try testing.expectEqualSlices(u8, "Just Just ", show3_writer.w.items);
}

const List = std.SinglyLinkedList;

pub fn ListCfg(comptime cfg: anytype) type {
    const Error = cfg.error_set;
    return struct {
        // Define Op constructor lambdas for StateF
        fn ListCtorDefs(comptime A: type) type {
            return struct {
                pub const Nil = NilLam;
                pub const Cons = ConsLam;

                const NilLam = extern struct {
                    lam_ctx: u64,

                    const Self = @This();
                    const NilLamCtx = void;
                    pub fn build() Self {
                        return .{ .lam_ctx = 0 };
                    }

                    pub fn deinit(self: Self) void {
                        _ = self;
                    }

                    pub fn call(self: Self) List(A) {
                        _ = self;
                        return .{ .first = null };
                    }
                };

                const ConsLam = extern struct {
                    len: u64,

                    const Self = @This();
                    const ConsLamCtx = []A;

                    pub fn build(len: u64) !Self {
                        return .{ .len = len };
                    }

                    pub fn deinit(self: Self) void {
                        _ = self;
                    }

                    pub fn call(self: *Self, as: []A) Error!List(A) {
                        assert(self.len == as.len);
                        var list: List(A) = .{ .first = null };
                        for (as) |a| {
                            const node = try cfg.allocator.create(List(A).Node);
                            node.* = .{ .next = null, .data = a };
                            list.prepend(node);
                        }
                        return list;
                    }
                };
            };
        }
    };
}

pub const ListCtxCfg = struct {
    allocator: Allocator,
    error_set: type,
};

fn getDefaultListCfg(allocator: Allocator) ListCtxCfg {
    return .{
        .allocator = allocator,
        .error_set = Allocator.Error,
    };
}

const ArrayListFunctorImpl = arraym.ArrayListMonadImpl;

pub const ListShowtNatImpl = struct {
    allocator: Allocator,

    const Self = @This();

    pub const F = List;
    pub const G = MWriterMaybe(ArrayList(u8));
    pub const Error = Allocator.Error;

    pub fn trans(self: Self, comptime A: type, fa: F(A)) Error!G(A) {
        var array = ArrayList(u8).init(self.allocator);
        if (fa.first) |first| {
            try array.appendSlice("[ ");
            const first_len = std.fmt.count("{any}", .{fa.first.data});
            const first_buf = array.addManyAsSliceAssumeCapacity(first_len);
            std.fmt.bufPrint(first_buf, "{any}", .{fa.first.data});

            var next = first.next;
            while (next) |node| {
                const len = std.fmt.count(", {any}", .{fa.first.data});
                const buf = array.addManyAsSliceAssumeCapacity(len);
                std.fmt.bufPrint(buf, ", {any}", .{fa.first.data});
                next = node.next;
            }
            try array.appendSlice(" ]");
            return .{ .a = first.data, .w = array };
        } else {
            // return empty ArrayList
            try array.appendSlice("[]");
            return .{ .a = @as(Maybe(A), null), .w = array };
        }
    }
};

fn listToA(comptime A: type) *const fn (a: List(A)) A {
    return struct {
        fn iterFn(a: List(A)) A {
            if (a.first) |first| {
                return first.data;
            } else return 0;
        }
    }.iterFn;
}

// test "FreeMonad(List, A) fmap" {
//     const allocator = testing.allocator;
//     const cfg = base.getDefaultBaseCfg(allocator);
//     const ListFunctor = Functor(ListFunctorImpl);
//     const list_functor = ListFunctor.init(.{ .none = {} });
//     const FreeMFunctor = Functor(FreeMonadImpl(cfg, List, ListFunctorImpl));
//     var freem_functor = FreeMFunctor.init(.{
//         .allocator = allocator,
//         .funf_impl = list_functor,
//     });
//
//     const ShowMonadImpl = MWriterMaybeMonadImpl(ArrayListMonoidImpl(u8), ArrayList(u8));
//     const ShowMonad = Monad(ShowMonadImpl);
//     const array_monoid = ArrayListMonoidImpl(u8){ .allocator = allocator };
//     const show_monad = ShowMonad.init(.{ .monoid_impl = array_monoid });
//     const NatListToShow = NatTrans(ListShowtNatImpl);
//     const nat_list_show = NatListToShow.init(.{ .allocator = allocator });
//
//     var a: u32 = 42;
//     _ = &a;
//     // const pure_freem = .{ .pure_m = a };
//     const pure_freem = FreeMonad(cfg, List, u32).pureM(@as(u32, 42));
//     const pure_freem1 = try freem_functor.fmap(.NewValMap, add_pi_f64, pure_freem);
//     try testing.expectEqual(45.14, try pure_freem1.iter(list_functor, listToA(f64)));
//     const show_writer = try pure_freem1.foldFree(nat_list_show, list_functor, show_monad);
//     defer show_writer.deinit();
//     try testing.expectEqual(45.14, show_writer.a);
//     try testing.expectEqualSlices(u8, "", show_writer.w.items);
//
//     const MaybeCtorEnum = std.meta.DeclEnum(MaybeCtorDefs(u32));
//     const Just: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Just);
//     const buildJust = MaybeCtorDefs(u32).Just.build;
//     // const Nothing: FOpEnumInt = @intFromEnum(MaybeCtorEnum.Nothing);
//     const FOpInfo = comptime FreeMonad(cfg, List, u32).FOpInfo;
//     const just_fns2 = &[_]FOpInfo{
//         .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
//         .{ .op_e = Just, .op_lam = @bitCast(buildJust()) },
//     };
//     const free_maybe = try pure_freem.appendFOps(@constCast(just_fns2));
//     defer free_maybe.deinit();
//     const free_maybe1 = try freem_functor.fmap(.NewValMap, add10, free_maybe);
//     defer free_maybe1.deinit();
//     try testing.expectEqual(52, try free_maybe1.iter(list_functor, listToA(u32)));
//     const show1_writer = try free_maybe1.foldFree(nat_list_show, list_functor, show_monad);
//     defer show1_writer.deinit();
//     try testing.expectEqual(52, show1_writer.a);
//     try testing.expectEqualSlices(u8, "Just Just ", show1_writer.w.items);
// }

const std = @import("std");
const base = @import("base.zig");
const applicative = @import("applicative.zig");

const TCtor = base.TCtor;
const isErrorUnionOrVal = base.isErrorUnionOrVal;

const Applicative = applicative.Applicative;

pub fn MonadFxTypes(comptime F: TCtor, comptime E: type) type {
    return struct {
        /// return type of bind
        pub fn MbType(comptime B: type) type {
            return E!F(B);
        }
    };
}

/// Monad typeclass like in Haskell, it inherit from Applicative Functor.
/// M is instance of Monad typeclass, such as Maybe, List
pub fn Monad(comptime MonadImpl: type) type {
    const M = MonadImpl.F;
    const has_sup_impl = @hasField(MonadImpl, "applicative_sup");

    return struct {
        // TODO: like std.io.Reader interface, add "monad_ctx: MonadCtx" field in it.
        const Self = @This();
        pub const InstanceImpl = MonadImpl;
        const ApplicativeSup = if (has_sup_impl)
            Applicative(InstanceImpl.SupImpl)
        else
            Applicative(InstanceImpl);

        pub const Error = InstanceImpl.Error;
        pub const MbType = InstanceImpl.MbType;

        const BindType = @TypeOf(struct {
            fn bindFn(
                instance: *InstanceImpl,
                comptime A: type,
                comptime B: type,
                // monad function: (a -> M b), ma: M a
                ma: M(A),
                k: *const fn (*InstanceImpl, A) MbType(B),
            ) MbType(B) {
                _ = instance;
                _ = ma;
                _ = k;
            }
        }.bindFn);

        pub fn init(instance: InstanceImpl) InstanceImpl {
            var inst: InstanceImpl = undefined;

            if (has_sup_impl) {
                const sup = ApplicativeSup.init(instance.applicative_sup);
                inst = instance;
                inst.applicative_sup = sup;
            } else {
                inst = ApplicativeSup.init(instance);
            }

            if (@TypeOf(InstanceImpl.bind) != BindType) {
                @compileError("Incorrect type of bind for Monad instance " ++ @typeName(InstanceImpl));
            }
            return inst;
        }
    };
}

fn GetPointerChild(comptime P: type) type {
    if (@typeInfo(P) != .Pointer) {
        @compileError("The type P must be a Pointer type!");
    }
    return std.meta.Child(P);
}

/// The do syntax for monad action, user pass a struct that include input parameters
/// and step functions of monad. The function finally return a monad value.
/// The name of do step function must be starts with "do" string.
/// The ctx_p parameter is pointer of a DoCtx value inputed by user.
pub fn runDo(ctx_p: anytype) DoRetType(GetPointerChild(@TypeOf(ctx_p))) {
    const DoCtx = GetPointerChild(@TypeOf(ctx_p));
    const info = comptime @typeInfo(DoCtx);
    if (info != .Struct) {
        @compileError("The ctx for runDo must be a struct!");
    }

    if (!@hasField(DoCtx, "monad_impl")) {
        @compileError("The ctx for runDo must has monad_impl field!");
    }

    if (!@hasDecl(DoCtx, "startDo")) {
        @compileError("The ctx for runDo must has startDo function!");
    }

    const MonadImpl = MonadImplType(DoCtx);
    // the first do step function
    const start_fn_info = @typeInfo(@TypeOf(@field(DoCtx, "startDo")));
    if (start_fn_info.Fn.params.len != 1) {
        @compileError("The first do step function must be only one parameters!");
    }

    const is_pure = DoCtx.is_pure;
    var impl_p = @constCast(&ctx_p.monad_impl);
    _ = &impl_p;
    const start_m = if (is_pure)
        // pure monad
        DoCtx.startDo(impl_p)
    else
        // impure monad
        try DoCtx.startDo(impl_p);
    const MT = @TypeOf(start_m);
    const has_err, const _MT = comptime isErrorUnionOrVal(MT);
    _ = has_err;
    const T = MonadImpl.BaseType(_MT);

    comptime var MR = MT;
    comptime var i = info.Struct.decls.len;
    comptime var isLastDoFn = true;
    // A composed continuation of do step functions for bind start_m
    comptime var k: ?*const fn (*MonadImpl, T) MR = null;
    inline while (i > 0) : (i -= 1) {
        const decl = info.Struct.decls[i - 1];
        if (comptime std.mem.startsWith(u8, decl.name, "do")) {
            const fn_info = @typeInfo(@TypeOf(@field(DoCtx, decl.name)));
            if (fn_info.Fn.params.len != 2) {
                @compileError("The do step function must be only two parameters!");
            }
            const A = fn_info.Fn.params[1].type.?;
            const MB = fn_info.Fn.return_type.?;
            if (isLastDoFn) {
                MR = MB;
                isLastDoFn = false;
            }

            const has_err_b, const _MB = comptime isErrorUnionOrVal(MB);
            _ = has_err_b;
            const B = MonadImpl.BaseType(_MB);
            const curr_k: ?*const fn (*MonadImpl, B) MR = @ptrCast(k);
            k = comptime @ptrCast(mkDoContFn(DoCtx, is_pure, A, MB, decl.name, curr_k));
        }
    }

    const has_err_r, const _MR = comptime isErrorUnionOrVal(MR);
    _ = has_err_r;
    const R = MonadImpl.BaseType(_MR);
    if (k) |_k| {
        // free intermediate monad for avoid memory leak
        defer MonadImpl.deinitFa(start_m, base.getFreeNothing(T));
        const final_k: *const fn (*MonadImpl, T) MR = @ptrCast(_k);
        if (is_pure) {
            return MonadImpl.bindWithCtx(T, R, impl_p, start_m, final_k);
        } else {
            return try impl_p.bind(T, R, start_m, final_k);
        }
    } else {
        return start_m;
    }
}

fn DoRetType(comptime DoCtx: type) type {
    const info = comptime @typeInfo(DoCtx);
    if (info != .Struct) {
        @compileError("The ctx for runDo must be a struct!");
    }

    comptime var i = info.Struct.decls.len;
    const MR = inline while (i > 0) : (i -= 1) {
        const decl = info.Struct.decls[i - 1];
        if (comptime std.mem.startsWith(u8, decl.name, "do")) {
            const fn_info = @typeInfo(@TypeOf(@field(DoCtx, decl.name)));
            break fn_info.Fn.return_type.?;
        }
    } else blk: {
        const fn_info = @typeInfo(@TypeOf(@field(DoCtx, "startDo")));
        break :blk fn_info.Fn.return_type.?;
    };
    return MR;
}

fn ContRetType(comptime K: type) type {
    const info = @typeInfo(K);
    const fn_info = @typeInfo(@typeInfo(info.Optional.child).Pointer.child);
    const MR = fn_info.Fn.return_type.?;
    return MR;
}

fn MonadImplType(comptime DoCtx: type) type {
    return std.meta.FieldType(DoCtx, .monad_impl);
}

fn mkDoContFn(
    comptime DoCtx: type,
    comptime is_pure: bool,
    comptime A: type,
    comptime MB: type,
    comptime fn_name: [:0]const u8,
    comptime k: anytype, // k is a optional of continuation function
) *const fn (*MonadImplType(DoCtx), A) ContRetType(@TypeOf(k)) {
    const MonadImpl = MonadImplType(DoCtx);
    const MR = ContRetType(@TypeOf(k));
    const has_err_r, const _MR = comptime isErrorUnionOrVal(MR);
    _ = has_err_r;
    const R = MonadImpl.BaseType(_MR);
    const do_cont = struct {
        fn doCont(impl: *MonadImpl, a: A) MR {
            const has_err1, const _MB = comptime isErrorUnionOrVal(MB);
            _ = has_err1;
            const B = MonadImpl.BaseType(_MB);

            const mb = if (is_pure)
                // pure monad
                @call(
                    .auto,
                    @field(DoCtx, fn_name),
                    .{ @constCast(impl), a },
                )
            else blk_f: {
                // impure monad
                // const ctx: *DoCtx = @alignCast(@fieldParentPtr("monad_impl", impl));
                // std.debug.print("call {s} ctx: {any}\n", .{ fn_name, ctx.* });
                // defer std.debug.print("after call {s} ctx: {any}\n", .{ fn_name, ctx.* });
                break :blk_f try @call(
                    .auto,
                    @field(DoCtx, fn_name),
                    .{ @constCast(impl), a },
                );
            };

            if (k) |_k| {
                // free intermediate monad for avoid memory leak
                defer MonadImpl.deinitFa(mb, base.getFreeNothing(B));
                if (is_pure) {
                    return MonadImpl.bindWithCtx(B, R, impl, mb, _k);
                } else {
                    return try @constCast(impl).bind(B, R, mb, _k);
                }
            } else {
                return mb;
            }
        }
    }.doCont;

    return do_cont;
}

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

/// The do syntax for monad action, user pass a struct that include input parameters
/// and step functions of monad. The function finally return a monad value.
/// The name of do step function must be starts with "do" string.
/// The ctx parameter is a struct value inputed by user.
pub fn runDo(ctx: anytype) DoRetType(@TypeOf(ctx)) {
    comptime var is_pure: bool = false;
    const CtxType = @TypeOf(ctx);
    const info = comptime @typeInfo(CtxType);
    if (info != .Struct) {
        @compileError("The ctx for runDo must be a struct!");
    }

    if (!@hasField(CtxType, "monad_impl")) {
        if (!@hasDecl(CtxType, "MonadType")) {
            @compileError("The ctx for runDo must has monad_impl field or MonadType declaration!");
        }
        is_pure = true;
    } else {
        if (@hasDecl(CtxType, "MonadType")) {
            @compileError("The ctx for runDo must not has both monad_impl field and MonadType declaration!");
        }
    }

    if (!@hasDecl(CtxType, "init")) {
        @compileError("The ctx for runDo must has init function!");
    }

    const MonadType = if (is_pure) CtxType.MonadType else void;
    const ImplType = if (is_pure) MonadType.InstanceImpl else @TypeOf(ctx.monad_impl);
    // the first do step function
    const init_fn_info = @typeInfo(@TypeOf(@field(CtxType, "init")));
    if (init_fn_info.Fn.params.len != 1) {
        @compileError("The first do step function must be only one parameters!");
    }
    const init_m = if (is_pure)
        // pure monad
        CtxType.init(@constCast(&ctx))
    else
        // impure monad
        try CtxType.init(@constCast(&ctx.monad_impl));
    const MT = @TypeOf(init_m);
    const has_err, const _MT = comptime isErrorUnionOrVal(MT);
    _ = has_err;
    const T = ImplType.BaseType(_MT);

    comptime var MR = MT;
    comptime var i = info.Struct.decls.len;
    comptime var isLastDoFn = true;
    const ImplOrCtxType = MonadImplOrCtxType(is_pure, CtxType);
    // A composed continuation of do step functions for bind init_m
    comptime var k: ?*const fn (*ImplOrCtxType, T) MR = null;
    inline while (i > 0) : (i -= 1) {
        const decl = info.Struct.decls[i - 1];
        if (comptime std.mem.startsWith(u8, decl.name, "do")) {
            const fn_info = @typeInfo(@TypeOf(@field(CtxType, decl.name)));
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
            const B = ImplType.BaseType(_MB);
            const curr_k: ?*const fn (*ImplOrCtxType, B) MR = @ptrCast(k);
            k = comptime @ptrCast(mkDoContFn(CtxType, is_pure, A, MB, decl.name, curr_k));
        }
    }

    const has_err_r, const _MR = comptime isErrorUnionOrVal(MR);
    _ = has_err_r;
    const R = ImplType.BaseType(_MR);
    if (k) |_k| {
        // free intermediate monad for avoid memory leak
        defer ImplType.deinitFa(init_m, base.getFreeNothing(T));
        const final_k: *const fn (*ImplOrCtxType, T) MR = @ptrCast(_k);
        if (is_pure) {
            return MonadType.bindWithCtx(T, R, @constCast(&ctx), init_m, final_k);
        } else {
            return try @constCast(&ctx.monad_impl).bind(T, R, init_m, final_k);
        }
    } else {
        return init_m;
    }
}

fn DoRetType(comptime CtxType: type) type {
    const info = comptime @typeInfo(CtxType);
    if (info != .Struct) {
        @compileError("The ctx for runDo must be a struct!");
    }

    comptime var i = info.Struct.decls.len;
    const MR = inline while (i > 0) : (i -= 1) {
        const decl = info.Struct.decls[i - 1];
        if (comptime std.mem.startsWith(u8, decl.name, "do")) {
            const fn_info = @typeInfo(@TypeOf(@field(CtxType, decl.name)));
            break fn_info.Fn.return_type.?;
        }
    } else blk: {
        const fn_info = @typeInfo(@TypeOf(@field(CtxType, "init")));
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

fn MonadImplOrCtxType(comptime is_pure: bool, comptime CtxType: type) type {
    return if (is_pure)
        // pure monad
        CtxType
    else
        // impure monad
        std.meta.FieldType(CtxType, .monad_impl);
}

fn mkDoContFn(
    comptime CtxType: type,
    comptime is_pure: bool,
    comptime A: type,
    comptime MB: type,
    comptime fn_name: [:0]const u8,
    comptime k: anytype, // k is a optional of continuation function
) *const fn (*MonadImplOrCtxType(is_pure, CtxType), A) ContRetType(@TypeOf(k)) {
    const ImplOrCtxType = MonadImplOrCtxType(is_pure, CtxType);
    const ImplType = if (is_pure) CtxType.MonadType.InstanceImpl else ImplOrCtxType;
    const MR = ContRetType(@TypeOf(k));
    const has_err_r, const _MR = comptime isErrorUnionOrVal(MR);
    _ = has_err_r;
    const R = ImplType.BaseType(_MR);
    const do_cont = struct {
        fn doCont(impl_or_ctx: *ImplOrCtxType, a: A) MR {
            const has_err1, const _MB = comptime isErrorUnionOrVal(MB);
            _ = has_err1;
            const B = ImplType.BaseType(_MB);

            const mb = if (is_pure)
                // pure monad
                @call(
                    .auto,
                    @field(CtxType, fn_name),
                    .{ @constCast(impl_or_ctx), a },
                )
            else
                // pure monad
                try @call(
                    .auto,
                    @field(CtxType, fn_name),
                    .{ @constCast(impl_or_ctx), a },
                );

            if (k) |_k| {
                // free intermediate monad for avoid memory leak
                defer ImplType.deinitFa(mb, base.getFreeNothing(B));
                if (is_pure) {
                    return CtxType.MonadType.bindWithCtx(B, R, impl_or_ctx, mb, _k);
                } else {
                    return try @constCast(impl_or_ctx).bind(B, R, mb, _k);
                }
            } else {
                return mb;
            }
        }
    }.doCont;

    return comptime do_cont;
}

const std = @import("std");
const base = @import("base.zig");
const applicative = @import("applicative.zig");
const maybe = @import("maybe.zig");
const arraym = @import("array_monad.zig");
const arraylm = @import("array_list_monad.zig");

const TCtor = base.TCtor;
const isErrorUnionOrVal = base.isErrorUnionOrVal;

const Applicative = applicative.Applicative;
const Maybe = base.Maybe;
const ArrayList = std.ArrayList;

pub fn MonadFxTypes(comptime F: TCtor, comptime E: ?type) type {
    return struct {
        /// return type of bind
        pub fn MbType(comptime B: type) type {
            if (E == null) return F(B);
            return E.?!F(B);
        }
    };
}

/// Monad typeclass like in Haskell, it inherit from Applicative Functor.
/// M is instance of Monad typeclass, such as Maybe, List
pub fn Monad(comptime M: TCtor) type {
    const MonadImpl = MonadImplFromTCtor(M);
    const ImplFVoid = if (@typeInfo(MonadImpl.F(void)) == .pointer)
        std.meta.Child(MonadImpl.F(void))
    else
        MonadImpl.F(void);
    const MVoid = if (@typeInfo(M(void)) == .pointer) std.meta.Child(M(void)) else M(void);
    if (MVoid != ImplFVoid) {
        @compileError("M type=" ++ @typeName(M(void)) ++ ", MonadImpl.F type=" ++ @typeName(MonadImpl.F(void)));
    }
    return MonadFromImpl(MonadImpl);
}

pub fn MonadFromImpl(comptime MonadImpl: type) type {
    _ = applicative.ApplicativeFromImpl(MonadImpl);
    const T = struct {
        pub const is_constrait = true;
        // TODO: like std.io.Reader interface, add "monad_ctx: MonadCtx" field in it.
        const Self = @This();
        const M = MonadImpl.F;
        pub const InstanceImpl = MonadImpl;

        pub const Error = InstanceImpl.Error;
        pub const MbType = InstanceImpl.MbType;

        const BindType = @TypeOf(struct {
            fn bindFn(
                instance: *const InstanceImpl,
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
    };

    if (@TypeOf(MonadImpl.bind) != T.BindType) {
        @compileError("Incorrect type of bind for Monad instance " ++ @typeName(MonadImpl));
    }
    return base.ConstraitType(T);
}

const monadImplMap = std.StaticStringMap(type).initComptime(.{
    .{ @typeName(Maybe(void)), maybe.MaybeMonadImpl },
    .{ @typeName(ArrayList(void)), arraylm.ArrayListMonadImpl },
    // Add more MonadImply and associated type
});

pub fn MonadImplFromTCtor(comptime F: TCtor) type {
    comptime {
        const T = F(void);
        switch (@typeInfo(T)) {
            .@"struct", .@"enum", .@"union", .@"opaque" => {
                if (@hasDecl(T, "MonadImpl")) {
                    return T.MonadImpl;
                }
            },
            .optional => return maybe.MaybeMonadImpl,
            .array => |info| return arraym.ArrayMonadImpl(info.len),
            .pointer => return std.meta.Child(T).MonadImpl,
            else => {},
        }

        const impl = monadImplMap.get(@typeName(T));
        if (impl == null) {
            @compileError("The customered Functor(" ++ @typeName(T) ++ ") must has MonadImpl!");
        }
        return impl.?;
    }
}

const GetPointerChild = base.GetPointerChild;

/// The do syntax for monad action, user pass a struct that include input parameters
/// and step functions of monad. The function finally return a monad value.
/// The name of do step function must be starts with "do" string.
/// The ctx_p parameter is pointer of a DoCtx value inputed by user.
pub fn runDo(ctx_p: anytype) DoRetType(GetPointerChild(@TypeOf(ctx_p))) {
    const DoCtx = GetPointerChild(@TypeOf(ctx_p));
    const info = comptime @typeInfo(DoCtx);
    if (info != .@"struct") {
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
    if (start_fn_info.@"fn".params.len != 1) {
        @compileError("The first do step function must be only one parameters!");
    }

    const is_pure = DoCtx.Error == null;
    var impl_p = @constCast(&ctx_p.monad_impl);
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
    comptime var i = info.@"struct".decls.len;
    comptime var isLastDoFn = true;
    // A composed continuation of do step functions for bind start_m
    comptime var k: ?*const fn (*const MonadImpl, T) MR = null;
    inline while (i > 0) : (i -= 1) {
        const decl = info.@"struct".decls[i - 1];
        if (comptime std.mem.startsWith(u8, decl.name, "do")) {
            const fn_info = @typeInfo(@TypeOf(@field(DoCtx, decl.name)));
            if (fn_info.@"fn".params.len != 2) {
                @compileError("The do step function must be only two parameters!");
            }
            const A = fn_info.@"fn".params[1].type.?;
            const MB = fn_info.@"fn".return_type.?;
            if (isLastDoFn) {
                MR = MB;
                isLastDoFn = false;
            }

            const has_err_b, const _MB = comptime isErrorUnionOrVal(MB);
            _ = has_err_b;
            const B = MonadImpl.BaseType(_MB);
            const curr_k: ?*const fn (*const MonadImpl, B) MR = @ptrCast(k);
            k = comptime @ptrCast(mkDoContFn(DoCtx, A, MB, decl.name, curr_k));
        }
    }

    const has_err_r, const _MR = comptime isErrorUnionOrVal(MR);
    _ = has_err_r;
    const R = MonadImpl.BaseType(_MR);
    if (k) |_k| {
        // free intermediate monad for avoid memory leak
        defer MonadImpl.deinitFa(start_m, base.getFreeNothing(T));
        const final_k: *const fn (*const MonadImpl, T) MR = @ptrCast(_k);
        if (is_pure) {
            return impl_p.bind(T, R, start_m, final_k);
        } else {
            return try impl_p.bind(T, R, start_m, final_k);
        }
    } else {
        return start_m;
    }
}

fn DoRetType(comptime DoCtx: type) type {
    const info = comptime @typeInfo(DoCtx);
    if (info != .@"struct") {
        @compileError("The ctx for runDo must be a struct!");
    }

    comptime var i = info.@"struct".decls.len;
    const MR = inline while (i > 0) : (i -= 1) {
        const decl = info.@"struct".decls[i - 1];
        if (comptime std.mem.startsWith(u8, decl.name, "do")) {
            const fn_info = @typeInfo(@TypeOf(@field(DoCtx, decl.name)));
            break fn_info.@"fn".return_type.?;
        }
    } else blk: {
        const fn_info = @typeInfo(@TypeOf(@field(DoCtx, "startDo")));
        break :blk fn_info.@"fn".return_type.?;
    };
    return MR;
}

fn ContRetType(comptime K: type) type {
    const info = @typeInfo(K);
    const fn_info = @typeInfo(@typeInfo(info.optional.child).pointer.child);
    const MR = fn_info.@"fn".return_type.?;
    return MR;
}

fn MonadImplType(comptime DoCtx: type) type {
    return std.meta.FieldType(DoCtx, .monad_impl);
}

fn mkDoContFn(
    comptime DoCtx: type,
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
    const is_pure = DoCtx.Error == null;
    const do_cont = &struct {
        fn doCont(impl: *const MonadImpl, a: A) MR {
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
            else
                // impure monad
                try @call(
                    .auto,
                    @field(DoCtx, fn_name),
                    .{ @constCast(impl), a },
                );

            if (k) |_k| {
                // free intermediate monad for avoid memory leak
                defer MonadImpl.deinitFa(mb, base.getFreeNothing(B));
                if (is_pure) {
                    return @constCast(impl).bind(B, R, mb, _k);
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

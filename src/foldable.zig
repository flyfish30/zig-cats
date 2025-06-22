const std = @import("std");
const base = @import("base.zig");
const monoid = @import("monoid.zig");
const maybe = @import("maybe.zig");
const arraym = @import("array_monad.zig");
const arraylm = @import("array_list_monad.zig");

const TCtor = base.TCtor;
const isErrorUnionOrVal = base.isErrorUnionOrVal;
const maybe_error = maybe.maybe_error;
const Monoid = monoid.Monoid;

const ArrayList = std.ArrayList;

pub fn FoldRetType(comptime E: ?type, comptime M: type) type {
    const Impl = Monoid(M).InstanceImpl;
    const Error = maybe_error.mappend(E, Impl.Error);
    return if (Error) |_Error| _Error!M else M;
}

/// Foldable typeclass like in Haskell.
/// F is instance of Foldable typeclass, such as Maybe, List
pub fn Foldable(comptime F: TCtor) type {
    const FoldableImpl = FoldableImplFromTCtor(F);
    const ImplFVoid = if (@typeInfo(FoldableImpl.F(void)) == .pointer)
        std.meta.Child(FoldableImpl.F(void))
    else
        FoldableImpl.F(void);
    const FVoid = if (@typeInfo(F(void)) == .pointer) std.meta.Child(F(void)) else F(void);
    if (FVoid != ImplFVoid) {
        @compileError("F type=" ++ @typeName(F(void)) ++ ", FoldableImpl.F type=" ++ @typeName(FoldableImpl.F(void)));
    }
    return FoldableFromImpl(FoldableImpl);
}

pub fn FoldableFromImpl(comptime FoldableImpl: type) type {
    const T = struct {
        pub const is_constrait = true;
        const Self = @This();
        const F = FoldableImpl.F;
        pub const InstanceImpl = FoldableImpl;

        pub const Error = InstanceImpl.Error;

        /// foldMap function type
        /// the type M must be a monoid instance
        const FoldMapType = @TypeOf(struct {
            fn foldMapFn(
                instance: *const InstanceImpl,
                comptime A: type,
                comptime M: type,
                // monoid instance for type M
                monoid_impl: Monoid(M).InstanceImpl,
                // map function: A -> M
                map_fn: *const fn (A) @TypeOf(monoid_impl).EM,
                fa: F(A),
            ) FoldRetType(Error, M) {
                _ = instance;
                _ = map_fn;
                _ = fa;
            }
        }.foldMapFn);

        /// foldl function type
        /// the type M must be a monoid instance
        const FoldlType = @TypeOf(struct {
            fn foldlFn(
                instance: *const InstanceImpl,
                comptime A: type,
                comptime M: type,
                // fold function: (M, A) -> M
                fold_fn: *const fn (M, A) Monoid(M).InstanceImpl.EM,
                init_val: M,
                fa: F(A),
            ) FoldRetType(Error, M) {
                _ = instance;
                _ = fold_fn;
                _ = init_val;
                _ = fa;
            }
        }.foldlFn);

        /// foldr function type
        /// the type M must be a monoid instance
        const FoldrType = @TypeOf(struct {
            fn foldrFn(
                instance: *const InstanceImpl,
                comptime A: type,
                comptime M: type,
                // fold function: (A, M) -> M
                fold_fn: *const fn (A, M) Monoid(M).InstanceImpl.EM,
                init_val: M,
                fa: F(A),
            ) FoldRetType(Error, M) {
                _ = instance;
                _ = fold_fn;
                _ = init_val;
                _ = fa;
            }
        }.foldrFn);

        /// foldMapLam function type
        /// the type M must be a monoid instance
        const FoldMapLamType = @TypeOf(struct {
            fn foldMapLam(
                instance: *const InstanceImpl,
                comptime A: type,
                comptime M: type,
                // monoid instance for type M
                monoid_impl: Monoid(M).InstanceImpl,
                // map lambda with function: *const fn (Self, A) EM
                map_lam: anytype,
                fa: F(A),
            ) FoldRetType(Error, M) {
                _ = instance;
                _ = map_lam;
                _ = monoid_impl;
                _ = fa;
            }
        }.foldMapLam);

        /// foldlLam function type
        /// the type M must be a monoid instance
        const FoldlLamType = @TypeOf(struct {
            fn foldlLam(
                instance: *const InstanceImpl,
                comptime A: type,
                comptime M: type,
                // foldl lambda with function: *const fn (Self, M, A) EM
                foldl_lam: anytype,
                init_val: M,
                fa: F(A),
            ) FoldRetType(Error, M) {
                _ = instance;
                _ = foldl_lam;
                _ = init_val;
                _ = fa;
            }
        }.foldlLam);

        /// foldrLam function type
        /// the type M must be a monoid instance
        const FoldrLamType = @TypeOf(struct {
            fn foldrLam(
                instance: *const InstanceImpl,
                comptime A: type,
                comptime M: type,
                // foldr lambda with function: *const fn (Self, A, M) EM
                foldr_lam: anytype,
                init_val: M,
                fa: F(A),
            ) FoldRetType(Error, M) {
                _ = instance;
                _ = foldr_lam;
                _ = init_val;
                _ = fa;
            }
        }.foldrLam);
    };

    if (@TypeOf(FoldableImpl.foldMap) != T.FoldMapType) {
        @compileError("Incorrect type of foldMap for Foldable instance " ++ @typeName(FoldableImpl));
    }
    if (@TypeOf(FoldableImpl.foldl) != T.FoldlType) {
        @compileError("Incorrect type of foldl for Foldable instance " ++ @typeName(FoldableImpl));
    }
    if (@TypeOf(FoldableImpl.foldr) != T.FoldrType) {
        @compileError("Incorrect type of foldr for Foldable instance " ++ @typeName(FoldableImpl));
    }
    if (@TypeOf(FoldableImpl.foldMapLam) != T.FoldMapLamType) {
        @compileError("Incorrect type of foldMapLam for Foldable instance " ++ @typeName(FoldableImpl));
    }
    if (@TypeOf(FoldableImpl.foldlLam) != T.FoldlLamType) {
        @compileError("Incorrect type of foldlLam for Foldable instance " ++ @typeName(FoldableImpl));
    }
    if (@TypeOf(FoldableImpl.foldrLam) != T.FoldrLamType) {
        @compileError("Incorrect type of foldrLam for Foldable instance " ++ @typeName(FoldableImpl));
    }
    return base.ConstraitType(T);
}

const foldableImplMap = std.StaticStringMap(type).initComptime(.{
    .{ @typeName(ArrayList(void)), arraylm.ArrayListFoldableImpl },
    // Add more FoldableImpl and associated types
});

pub fn FoldableImplFromTCtor(comptime F: TCtor) type {
    comptime {
        const T = F(void);
        switch (@typeInfo(T)) {
            .@"struct", .@"enum", .@"union", .@"opaque" => {
                if (@hasDecl(T, "FoldableImpl")) {
                    return T.FoldableImpl;
                }
            },
            .optional => {
                // For Maybe/Optional, would need a FoldableImpl in maybe.zig
                @compileError("Optional Foldable instance not implemented yet");
            },
            .array => |info| {
                // For arrays, return ArrayFoldableImpl from array_monad.zig
                return arraym.ArrayFoldableImpl(info.len);
            },
            .pointer => return std.meta.Child(T).FoldableImpl,
            else => {},
        }

        const impl = foldableImplMap.get(@typeName(T));
        if (impl == null) {
            @compileError("The customered Foldable(" ++ @typeName(T) ++ ") must has FoldableImpl!");
        }
        return impl.?;
    }
}

/// Common implementation of foldMap using foldl
pub fn commonFoldMap(
    comptime A: type,
    comptime M: type,
    comptime Error: ?type,
    foldable_impl: anytype,
    monoid_impl: Monoid(M).InstanceImpl,
    map_fn: *const fn (A) @TypeOf(monoid_impl).EM,
    fa: anytype,
) FoldRetType(Error, M) {
    const fold_lam = struct {
        map_fn: *const fn (A) M,
        monoid_impl: @TypeOf(monoid_impl),

        const Self = @This();
        fn call(self: *const Self, acc: M, a: A) M {
            const mapped = self.map_fn(a);
            const result = if (Error == null)
                self.monoid_impl.mappend(acc, mapped)
            else
                self.monoid_impl.mappend(acc, mapped) catch |err| {
                    base.deinitOrUnref(acc);
                    base.deinitOrUnref(mapped);
                    return err;
                };

            // Free intermediate values if needed
            base.deinitOrUnref(acc);
            base.deinitOrUnref(mapped);
            return result;
        }
    }{ .map_fn = map_fn, .monoid_impl = monoid_impl };

    const init_val = if (Error == null) monoid_impl.mempty() else try monoid_impl.mempty();
    return if (Error == null)
        foldable_impl.foldlLam(A, M, fold_lam, init_val, fa)
    else
        try foldable_impl.foldlLam(A, M, fold_lam, init_val, fa);
}

/// Common implementation of foldr using foldl (not the most efficient but works)
pub fn commonFoldr(
    comptime A: type,
    comptime M: type,
    comptime Error: ?type,
    foldable_impl: anytype,
    fold_fn: *const fn (A, M) @TypeOf(foldable_impl).EM,
    init_val: M,
    fa: anytype,
) FoldRetType(Error, M) {
    // For ArrayList, we can implement foldr by iterating backwards
    // This is a simple implementation; a more generic one would convert to a list first
    const flip_lam = struct {
        fold_fn: *const fn (A, M) @TypeOf(foldable_impl).EM,
        const FlipSelf = @This();
        pub fn call(self: *const FlipSelf, b: M, a: A) M {
            return self.fold_fn(a, b);
        }
    }{ .fold_fn = fold_fn };

    return if (Error == null)
        foldable_impl.foldlLam(A, M, flip_lam, init_val, fa)
    else
        try foldable_impl.foldlLam(A, M, flip_lam, init_val, fa);
}

const testing = std.testing;

test "Foldable ArrayList typeclass usage example" {
    const allocator = testing.allocator;

    // Create Foldable for ArrayList
    const ArrayListFoldable = Foldable(ArrayList);
    const foldable_impl = ArrayListFoldable.InstanceImpl{ .allocator = allocator };

    // Create test data
    var numbers = ArrayList(u32).init(allocator);
    defer numbers.deinit();
    try numbers.appendSlice(&[_]u32{ 1, 2, 3, 4, 5 });

    // Test foldl - sum all numbers
    const sum = foldable_impl.foldl(u32, u32, struct {
        fn add(acc: u32, x: u32) u32 {
            return acc + x;
        }
    }.add, 0, numbers);
    try testing.expectEqual(@as(u32, 15), sum);

    // Test foldr - construct a list in reverse
    const product = foldable_impl.foldr(u32, u32, struct {
        fn mul(x: u32, acc: u32) u32 {
            return if (acc == 0) x else x * acc;
        }
    }.mul, 1, numbers);
    try testing.expectEqual(@as(u32, 120), product);

    // Test foldMap - sum of squares using u32 monoid
    const U32Monoid = monoid.Monoid(u32);
    const u32_monoid = U32Monoid.InstanceImpl{};

    const sum_of_squares = foldable_impl.foldMap(u32, u32, u32_monoid, struct {
        fn square(x: u32) u32 {
            return x * x;
        }
    }.square, numbers);
    try testing.expectEqual(@as(u32, 55), sum_of_squares); // 1² + 2² + 3² + 4² + 5² = 1 + 4 + 9 + 16 + 25 = 55
}

test "Foldable with lambda functions" {
    const allocator = testing.allocator;

    const ArrayListFoldable = Foldable(ArrayList);
    const foldable_impl = ArrayListFoldable.InstanceImpl{ .allocator = allocator };

    var strings = ArrayList([]const u8).init(allocator);
    defer strings.deinit();
    try strings.appendSlice(&[_][]const u8{ "Hello", " ", "World", "!" });

    // Test foldlLam - concatenate strings with lambda
    const concat_lam = struct {
        pub fn call(_: *const @This(), acc: usize, s: []const u8) usize {
            return acc + s.len;
        }
    }{};

    const total_len = foldable_impl.foldlLam([]const u8, usize, concat_lam, 0, strings);
    try testing.expectEqual(@as(usize, 12), total_len); // "Hello" + " " + "World" + "!" = 5 + 1 + 5 + 1 = 12
}

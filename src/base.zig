//! All base types and functions for zig-cats
const std = @import("std");
const Allocator = std.mem.Allocator;

// pub usingnamespace @import("base_types.zig");

/// A single-argument type function for type constructor
pub const TCtor = *const fn (comptime type) type;

pub fn GetPointerChild(comptime P: type) type {
    if (@typeInfo(P) != .Pointer) {
        @compileError("The type P must be a Pointer type!");
    }
    return std.meta.Child(P);
}

pub fn MapFnInType(comptime MapFn: type) type {
    const len = @typeInfo(MapFn).Fn.params.len;

    if (len != 1) {
        @compileError("The map function must has only one parameter!");
    }

    return @typeInfo(MapFn).Fn.params[0].type.?;
}

pub fn MapFnRetType(comptime MapFn: type) type {
    const R = @typeInfo(MapFn).Fn.return_type.?;

    if (R == noreturn) {
        @compileError("The return type of map function must not be noreturn!");
    }
    return R;
}

pub fn MapLamInType(comptime MapLam: type) type {
    const info = @typeInfo(MapLam);
    if (info != .Struct) {
        @compileError("The map lambda must be a struct!");
    }

    const mapFnInfo = @typeInfo(@TypeOf(MapLam.call));
    const len = mapFnInfo.Fn.params.len;

    if (len != 2) {
        @compileError("The call function of map lambda must have only two parameters!");
    }
    if (mapFnInfo.Fn.params[0].type.? != *MapLam and mapFnInfo.Fn.params[0].type.? != *const MapLam) {
        @compileError("The first parameter of call function must be a pointer of MapLam!");
    }

    return mapFnInfo.Fn.params[1].type.?;
}

pub fn MapLamRetType(comptime MapLam: type) type {
    const info = @typeInfo(MapLam);
    if (info != .Struct) {
        @compileError("The map lambda must be a struct!");
    }

    const mapFnInfo = @typeInfo(@TypeOf(MapLam.call));
    const R = mapFnInfo.Fn.return_type.?;

    if (R == noreturn) {
        @compileError("The return type of call function must not be noreturn!");
    }
    return R;
}

pub fn AnyMapFn(a: anytype, b: anytype) type {
    return fn (@TypeOf(a)) @TypeOf(b);
}

/// The kind of map function for new a translated value or inplace replaced by
/// translated value.
pub const MapFnKind = enum {
    /// Need new a value for translated value, the caller should to free new
    /// value.
    NewValMap,
    /// Need new a value for translated value, the caller should to free new
    /// value.
    /// The input value of map function is a reference.
    /// The fa paramerter of fmap function is also a reference.
    NewValMapRef,
    /// Just inplace replace with translated value, the bitsize of translated
    /// value must equal bitsize of origin value.
    InplaceMap,
    /// Just inplace replace with translated value, the bitsize of translated
    /// value must equal bitsize of origin value.
    /// The input value of map function is a reference.
    /// The fa paramerter of fmap function is also a reference.
    InplaceMapRef,
};

pub fn isInplaceMap(comptime K: MapFnKind) bool {
    return K == .InplaceMap or K == .InplaceMapRef;
}

pub fn isMapRef(comptime K: MapFnKind) bool {
    return K == .NewValMapRef or K == .InplaceMapRef;
}

/// The mode of fmap is used to indicate whether the map function has a self
/// parameter.
pub const FMapMode = enum {
    /// The map function has only a input parameter.
    NormalMap,
    /// The map function is a lambda struct that has a map function with a
    /// self parameter.
    LambdaMap,
};

/// A identity function as unit of endofunctions
fn identity(a: anytype) @TypeOf(a) {
    return a;
}

/// Check the type E whether it is a ErrorUnion, if true then return a under
/// type of ErrorUnion, else just return type E.
pub fn isErrorUnionOrVal(comptime E: type) struct { bool, type } {
    const info = @typeInfo(E);
    const has_error = if (info == .ErrorUnion) true else false;
    const A = if (has_error) info.ErrorUnion.payload else E;
    return .{ has_error, A };
}

pub fn castInplaceValue(comptime T: type, val: anytype) T {
    const info = @typeInfo(@TypeOf(val));
    switch (info) {
        .Optional => {
            const v = val orelse return null;
            return castInplaceValue(std.meta.Child(T), v);
        },
        .Struct => {
            if (info.Struct.layout == .auto) {
                @compileError("Can't inplace cast struct with auto layout");
            }
            return @bitCast(val);
        },
        else => {
            return @bitCast(val);
        },
    }
}

pub fn defaultVal(comptime T: type) T {
    const info_a = @typeInfo(T);
    if (info_a == .Fn) {
        return getDefaultFn(T);
    } else if (info_a == .Pointer and @typeInfo(std.meta.Child(T)) == .Fn) {
        return getDefaultFn(std.meta.Child(T));
    }
    return std.mem.zeroes(T);
}

pub fn getDefaultFn(comptime Fn: type) fn (MapFnInType(Fn)) MapFnRetType(Fn) {
    return struct {
        const A = MapFnInType(Fn);
        const B = MapFnRetType(Fn);
        fn defaultFn(a: A) B {
            _ = a;
            return std.mem.zeroes(B);
        }
    }.defaultFn;
}

pub fn Maybe(comptime A: type) type {
    return ?A;
}

pub fn Array(comptime len: usize) TCtor {
    return struct {
        fn ArrayF(comptime A: type) type {
            return [len]A;
        }
    }.ArrayF;
}

pub fn FreeTFn(comptime T: type) type {
    return *const fn (T) void;
}

/// A empty free function, do nothing
pub fn getFreeNothing(comptime T: type) FreeTFn(T) {
    return struct {
        fn freeT(a: T) void {
            _ = a;
        }
    }.freeT;
}

/// A empty free function, do nothing
pub fn freeNothing(a: anytype) void {
    _ = a;
    return;
}

/// Clone a constructed data or referance a pointer
pub fn copyOrCloneOrRef(a: anytype) !@TypeOf(a) {
    const T = @TypeOf(a);
    const info = @typeInfo(T);
    switch (info) {
        .Struct, .Enum, .Union, .Opaque => {
            if (@hasDecl(T, "clone")) {
                return a.clone();
            }
        },
        .Pointer => {
            const Child = info.Pointer.child;
            const c_info = @typeInfo(Child);
            if (info.Pointer.size != .One) {
                @compileError("deinitOrUnref only for pointer that has only one element!");
            }
            switch (c_info) {
                .Struct, .Enum, .Union, .Opaque => {
                    if (@hasDecl(T, "strongRef")) {
                        return a.strongRef();
                    }
                },
                else => {},
            }
        },
        else => {},
    }

    return a;
}

/// get a normal deinit or unreference function for free some memory
pub fn getDeinitOrUnref(comptime T: type) FreeTFn(T) {
    return struct {
        fn freeT(a: T) void {
            deinitOrUnref(a);
        }
    }.freeT;
}

/// Deinit a constructed data or unreferance a pointer
pub fn deinitOrUnref(a: anytype) void {
    const T = @TypeOf(a);
    const info = @typeInfo(T);
    switch (info) {
        .Struct, .Enum, .Union, .Opaque => {
            if (@hasDecl(T, "deinit")) {
                a.deinit();
            }
        },
        .Pointer => {
            const Child = info.Pointer.child;
            const c_info = @typeInfo(Child);
            if (info.Pointer.size != .One) {
                @compileError("deinitOrUnref only for pointer that has only one element!");
            }
            switch (c_info) {
                .Struct, .Enum, .Union, .Opaque => {
                    if (@hasDecl(T, "strongUnref")) {
                        _ = a.strongUnref();
                    }
                },
                else => {},
            }
        },
        else => {},
    }
}

# Zig programming tips

This file is collection of some tips for Zig programming.

### Const function pointer

The  function as first class value should must be a const function pointer, the type form is: *const fn(A) B . If you use a value of Fn type as parameter and pass it to a generic function with an anytype parameter, you may get a compilation error: "unable to resolve comptime value".


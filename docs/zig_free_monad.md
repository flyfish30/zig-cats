#                  Zig语言的Free Monad实现

Zig语言是我最喜欢的语言之一，是一门非常优秀的系统级的底层编程语言，是C语言的革新式演变的替代者，能够和C无缝的交互。因此其对函数式编程的支持是非常少的，我在使用这门语言几个月后，发现Zig语言的comptime能力非常强大，于是便有了在Zig语言中支持函数式编程的想法。在翻阅了一些资料，查看了Zig的Std标准库的源代码后，我实现了一些基本的函数式编程的支持，比如函子、可应用函子、单子、幺半群、ADT、函子的组合等。

在完成了上面这些后，我注意到了Free Monad这个函数式编程中非常有用的数据类型，想用Zig语言来实现Free Monad。然而，Zig语言毕竟还是命令式语言，不支持lambda，又没有自动内存管理，在开始实现Free Monad后，发现这个过程困难重重，充满了看似不可逾越的障碍。经历过多次近乎绝望的冥思苦想后，终于柳暗花明又一村，完成了基本的Free Monad的支持。后续就是一些性能的优化、易用性方面的支持，更多的Free Monad的实例的支持和实现了。

现在，我就带领大家来看看如何使用Zig语言来实现Free Monad的，这趟旅程结束后，大家将会对Free Monad的本质有一个清晰的认识，从而更好的利用Free Monad来设计灵活的程序。我用Zig语言实现的Free Monad是完全等价于Haskell中的Free Monad的，因此在下面的讲解中会使用Haskell的代码来说明一些重要的概念和设计。

Free Monad在函数式编程中是非常有实用价值的一个数据类型，有非常多的资料介绍了Free Monad是什么，有什么价值和意义，具体的实用例子有哪些，这里就不多介绍了。我们先来看Haskell中的Free Moand的定义，具体的定义如下：

```haskell
data Free f a = Pure a
              | Free (f (Free f a))
```

这是一个递归定义的和类型，一个Free Monad可能是一个纯的值a，也可能是一个不纯的由下一层的Free f a构成的值。将这个Free f a的某一个值展开，我们可以得到下面这样的形式：

```haskell
free_ma = Free (Op2 (Free (Op3 (Free (Op0 (Pure 42))))))
```

可以看到，Free Monad很像一个由多个操作指令组成的列表，上面的Free Monad的值就是一个由三个操作指令Op2、Op1、Op0组成的列表。其中函子f 是OpInstruction，其定义如下所示：

```haskell
data OpInstruction a = Op0 a | Op1 a | Op2 a
```

这是一个简单的函子f 的示例。更复杂的情况不会影响Free Monad本质上是一个由多个操作指令组成的列表的事实。

Free Monad是一个由函子f 自由的组合起来得到的一个新数据类型，自动的具有Monad的结构，因此叫自由单子(Free Monad)。当然也是一个函子和可应用函子。我们接下来看看Free Monad的函子实例的定义：

```haskell
instance Functor f => Functor (Free f) where
  fmap f (Pure a)  = Pure (f a)
  fmap f (Free fm) = Free (fmap (fmap f) fm)
```

因为Free Monad是一个递归定义的和类型，所以其fmap函数的实现也是递归定义的。看起来似乎不大好理解，但其实就是将(fmap f) 通过Free (fmap (fmap f) fm)中的第一个fmap 来穿过层层函子F 的结构传递下去， 最终到达纯的值Pure a，然后简单的将函数f 应用到值a 上，得到一个新的纯的值Pure (f a)。将这个纯的值Pure (f a)再通过层层函子F 的构造得到最终的Free Monad的值。其中每一层函子F 都对传递(fmap f) 提供了一个通路，所有层的函子F 一起组成了一个完整的传递fmap f 的通路。

再来看Free Monad的可应用函子实例的定义：

```haskell
instance Functor f => Applicative (Free f) where
  pure = Pure
  (Pure g) `fapply` x = fmap g x
  (Free fm) `fapply` x = Free (fmap (`fapply` x) fm)
```

这也同样有一个递归定义的函数fapply。为了代码更直观，这里使用了Haskell的中缀表示形式来定义函数fapply。和fmap函数的实现类似，也是将 ```(`fapply` af)``` 通过fmap来穿过层层函子F 的结构传递下去， 最终到达纯的值Pure g，此时不通过的是取出函数g，对x 再次应用fmap g，会得到一个新的Free Monad的值。将这个值再通过层层函子F 的构造得到最终的Free Monad的值。同样的，所有层的函子F 一起组成了一个完整的传递 ```(`fapply` af)``` 的通路。

最后我们来看Free Monad的单子实例的定义：

```haskell
instance Functor f => Monad (Free f) where
  (Pure a) `bind` k = k a
  (Free fm) `bind` k = Free (fmap (`bind` k) fm)
```

这里同样使用了递归定义来实现bind函数，并使用了Haskell的中缀表示形式。和fapply函数的实现类似，也是将 ```(`bind` k)``` 通过fmap来穿过层层函子F 的结构传递下去， 最终到达纯的值Pure a，不同的是直接将函数k 应用到值a 上，得到一个新的Free Monad的值。将这个值再通过层层函子F 的构造得到最终的Free Monad的值。同样的，所有层的函子F 一起组成了一个完整的传递 ```(`bind` k)``` 的通路。

有了Free Monad的单子实例的定义后，我们就可以说Free 这个类型构造子将任意一个函子f 提升为一个单子，也就是Free f 是一个单子。那这个新构造出的Free f单子有什么意义呢？

我们构造了一个Free f 这个Free Monad后，提供一个函子f 到普通单子m 的自然变换eta: forall a. f a -> m a，就可以将值Free f a求值为一个普通的单子的值m a。如果这个单子m 是一个复杂的可运行的结构，我们可以再次运行这个单子的值m a，得到一个更简化的值。如果这个m 是一个State s单子，我们可以提供一个初始的状态s0，运行State s a后得到一个最终的状态final_s和新的a的值。如果这个m 是一个Io单子，那我们就可以运行这个Io a程序后得到一个Io 操作的结果。

这个将Free f a求值为普通单子的值m a的函数叫foldFree，其具体定义如下：

```haskell
foldFree :: (Functor f, Monad m)
         => (forall a. f a -> m a) -> (forall a. Free f a -> m a)
foldFree eta (Pure a)  = pure a
foldFree eta (Free fm) = join (eta (fmap (foldFree eta) fm))
```

这同样是一个递归定义的函数。其在Free Monad的每一层都做了将Free f a求值为m a的变换，当遇到最底层的纯的值Pure a时，只是简单的使用单子m 的pure 函数应用到a 上，得到一个新的纯的m a 的值。随后，在每一层将变换后得到的值m (m a) 通过应用join 函数变为值m a。最终，在多次应用join 函数后，得到一个单一的单子的值m a。

从上面Free Monad的定义可以看到，Free Monad只是简单的将函子F 拼成一个多层的结构，并没有做具体的事情。而负责将函子F 拼成一个多层结构的就是Free Monad的值构造子Free。对应的，Free Monad的另一个值构造子Pure只负责提供一个纯的Free Monad的值。显然，这个值构造子Free是没有具体的组合语义的抽象的构造子，就像一个抽象的胶水把多个函子F 粘起来。值构造子Free 拼出来的这个多层结构的Free Monad是函子F 的操作指令的组合，利用foldFree函数，我们可以将函子F 的操作指令的解释和组合解耦分离，互不干扰。

单子的do语法可以用来表示函子F 的操作指令的组合的形式，也就是有些什么操作指令，以及这些操作指令的次序。这个操作指令的组合的形式可以看成一个DSL的程序。foldFree函数的自然变换会将每一个操作指令解释为有具体意义的行为，也就是值m a，而普通单子m 的join函数则给予了Free 这个抽象胶水具体的组合语义，将多层的m (m... (m a)) 这样的值组合为单个的m a。

**简单的来说，foldFree函数中的普通单子m 解释了Free Monad，单子m 的join函数将每一层的操作指令的解释也就是值m a组合起来，得到一个单一的值m a。只要提供不同的自然变换eta，将同样的Free Monad的值Free f a 求值为不同的单子m 的值m a，就可以得到不同的Free Monad的解释。** 

这也是Free Monad存在的意义。

有了上面这些对Free Monad的定义和实现的介绍，及Free Monad的求值方法，我们就可以着手使用Zig语言来实现Free Monad了。

我们再来回顾一下Free Monad的定义：

```haskell
data Free f a = Pure a
              | Free (f (Free f a))
```

可以看到，这是一个有两个值构造子Pure和Free 的和类型。另外，Free是一个接受一个函子类型f 和普通类型a 这两个参数的高阶类型。在Zig语言中，函子类型可以用类型函数来表示，接受函子类型参数的高阶类型则用接受类型函数为参数的类型函数来表示，可以称其为高阶类型函数。因此，Free Monad的类型可以用如下的高阶类型函数来表示。

```c
fn FreeMonad(comptime F: TCtor, comptime A: type) type {
  ...
}
```

其中的参数F 是一个函子类型，用类型TCtor来标示参数F的类型。而类型TCtor则是一个类型函数，其定义如下：

```c
const TCtor = *const fn (comptime type) type;
```

Zig语言中，实现和类型使用经典的tagged union就可以了。上面说了Free 将函子F 拼成一个多层结构，实际上这个多层结构就是由多个函子F 的操作指令组成的列表，这里使用了递归定义来实现这个列表。在Zig语言中，列表可以用一个高效的数据类型ArrayList来表示，而为了表示递归定义，则需要一个指向本数据类型的指针。于是，就有了下面这个Zig语言的Free Monad的定义：

```c
pub fn FreeM(comptime F: TCtor) TCtor {
    return struct {
        fn FreeF(comptime A: type) type {
            return union(enum) {
                pure_m: A,
                free_m: struct { *Self, ArrayList(FOpInfo) },

                const Self = @This();
                const BaseType = A;

                // The building information of operator in F for FreeMonad(F, A)
                pub const FOpInfo = struct {
                    op_e: FOpEnumInt,
                    op_lam: AnyOpLam,
                };
              
              // more other codes
              ...
            };
        }
    }.FreeF;;
}

pub fn FreeMonad(comptime F: TCtor, comptime A: type) type {
    return FreeM(F)(A);
}
```

在上面的Free Monad的定义中，FreeMonad函数返回了一个tagged union的数据类型，FreeM是FreeMonad的柯里化形式。这个tagged union的pure_m和free_m这两个tag分别对应了Free f a的定义中的Pure和Free这两个值构造子。其中，pure_m这个值构造子的实现很简单，就是一个类型为A的值。而free_m这个值构造子则是一个二元组，第一个元素是递归定义使用的*Self类型，一般保存的是纯的值，第二个元素则是操作指令的列表ArrayList(FOpInfo)，为了程序优化的需要，这里的操作指令是按组合时的逆序保存的。

操作指令的构造信息是由类型FOpInfo提供的，op_e是一个用于表示操作指令类别的枚举值对应的整数，对应上面的函子OpInstruction的定义中的值构造子Op0、Op1、Op2。op_lam则是从类型A 的值构造出函子F 对应的类型F A的值的lambda函数。这个lambda函数的类型是A -> F A，注意到这里的类型参数A 是多态的，所以这实际上就是一个自然变换。这是因为Zig没有Haskell中的原生ADT模式匹配支持的一个设计，同时也是针对Haskell中的Free Monad的实现的一个高效优化的设计所需要的。

我们知道，Haskell中的Free Monad的实现是非常低效的，原因在于在调用Free Monad的fmap、fapply和bind函数时，每次都需要遍历操作指令组成的列表。多次调用这些函数后，会多次遍历这个列表，效率非常低。而实际上，每次遍历这个列表，只是传递(fmap f)、 ```(`fapply` af)```和```(`bind` k)``` 这些最终只在纯的值中起作用的计算而已，每一步的遍历并没有有用的计算。所以，我将这些操作指令列表的自上而下的传递改为自下而上的构造。也就是不像Haskell的实现那样，在操作指令列表中直接保存函子F 的操作指令对应的Op0 a这样的值了。而是保存的从值a 构造出函子F 的操作指令对应的Op0 a这样的值的lambda函数，也就是FOpInfo中的op_lam。这样，每次调用fmap、fapply和bind函数时，就不需要遍历操作指令组成的列表了。

于是，我们就有了下面的fmap函数的定义:

```c
        pub fn fmap(
            self: *Self,
            comptime K: MapFnKind,
            map_fn: anytype,
            fa: FaType(K, @TypeOf(map_fn)),
        ) FbType(@TypeOf(map_fn)) {
            // const A = MapFnInType(@TypeOf(map_fn));
            const B = MapFnRetType(@TypeOf(map_fn));
            const has_err, const _B = comptime isErrorUnionOrVal(B);

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
                const new_pure_m = try self.allocator.create(FreeMonad(FunF, _B));
                new_pure_m.* = .{ .pure_m = _b };
                return .{ .free_m = .{ new_pure_m, try fa.free_m[1].clone() } };
            }
        }
```

忽略掉那些类型计算和错误处理部分的代码，以及引用类型的特别处理，fmap函数的实现是很简单的。获取原来的Free monad的纯的值中的a，应用map_fn函数，得到新的值b。使用新的值b构造出新的Free Monad的值，操作指令列表不作任何处理，只是简单的拷贝而已。可以看到，使用这种自下而上的构造的方式优化后，没有了对参数fa中的操作指令列表遍历的过程，fmap函数的性能得到了极大的提升。

接下来我们来看fapply函数的实现，其代码如下：

```c
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

            const map_fn = ff.free_m[0].pure_m;
            if (fa == .pure_m) {
                const b = map_fn(fa.pure_m);
                const _b = if (has_err) try b else b;
                const new_pure_m = try self.allocator.create(F(_B));
                new_pure_m.* = .{ .pure_m = _b };
                return .{ .free_m = .{ new_pure_m, try ff.free_m[1].clone() } };
            } else {
                const b = map_fn(fa.free_m[0].pure_m);
                const _b = if (has_err) try b else b;
                const new_pure_m = try self.allocator.create(F(_B));
                new_pure_m.* = .{ .pure_m = _b };
                const len = fa.free_m[1].items.len + ff.free_m[1].items.len;
                var flist = try @TypeOf(fa.free_m[1]).initCapacity(self.allocator, len);
                flist.appendSliceAssumeCapacity(fa.free_m[1].items);
                flist.appendSliceAssumeCapacity(ff.free_m[1].items);
                return .{ .free_m = .{ new_pure_m, flist } };
            }
        }
```

和fmap函数稍有不同，如果第一个参数ff 这个Free Monad是一个纯的值，则fapply退化为fmap函数。其他的情况下，则取出参数ff 中的纯的值中的函数，将这个函数应用到参数fa 中纯的值，得到新的值b。然后将参数ff 和fa 中的操作指令列表连接成一个新的操作指令列表，和新的值b一起构造出新的Free Monad的值并返回。同样的，没有了对参数fa 和ff 中的操作指令列表遍历的过程，fapply函数的性能得到了极大的提升。

继续来看bind函数的实现，其代码如下：

```c
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

            const freem = try k(self, ma.free_m[0].pure_m);
            if (freem == .pure_m) {
                const new_pure_m = try self.allocator.create(F(B));
                new_pure_m.* = .{ .pure_m = freem.pure_m };
                return .{ .free_m = .{ new_pure_m, try ma.free_m[1].clone() } };
            } else {
                var flist = freem.free_m[1];
                try flist.appendSlice(ma.free_m[1].items);
                return .{ .free_m = .{ freem.free_m[0], flist } };
            }
        }
```

可以看到，代码的实现也是很简单。如果参数ma 这个Free Monad是一个纯的值，则取出ma 中纯的值，将函数k 应用到这个值，将结果直接返回。其他情况下，则取出参数ma 中纯的值，将其应用到函数k 上，得到一个新的Free Monad到值freem。然后，将参数ma 和freem 中的操作指令列表连接成一个新的操作指令列表，和freem中纯的值一起构造出新的Free Monad的值并返回。同样没有操作指令列表的遍历操作，而操作指令列表的连接在Zig语言中使用的是ArrayList的appendSlice函数，这个函数非常高效。因此，bind函数的性能也是非常高的。

最后，我们来看Free Monad的求值函数foldFree的实现，其代码如下：

```c
                pub fn foldFree(
                    self: Self,
                    nat_impl: anytype,
                    m_impl: anytype,
                ) @TypeOf(m_impl).MbType(A) {
                    const NatImpl = @TypeOf(nat_impl);
                    const MImpl = @TypeOf(m_impl);
                    comptime assert(F == NatImpl.F);
                    comptime assert(MImpl.F == NatImpl.G);
                    if (self == .pure_m) {
                        return @constCast(&m_impl).pure(self.pure_m);
                    }

                    var acc_m = try @constCast(&m_impl).pure(self.free_m[0].pure_m);
                    for (self.free_m[1].items) |op_info| {
                        const fm_op_ctors = GetOpCtors(F, MImpl.F(A));
                        const val_ctor_info = fm_op_ctors[op_info.op_e];
                        const f_acc_m = val_ctor_info.callValCtorFn(
                            op_info.op_lam,
                            @constCast(&[_]MImpl.F(A){acc_m}),
                        );
                        const m_acc_m = try nat_impl.trans(MImpl.F(A), f_acc_m);
                        acc_m = try @constCast(&m_impl).join(A, m_acc_m);
                        MImpl.deinitFa(m_acc_m, base.getDeinitOrUnref(MImpl.F(A)));
                    }
                    return acc_m;
                }
```

foldFree函数的第一个参数self 就是一个Free Monad，第二个参数nat_impl是自然变换的一个实例，对应Haskell中foldFree函数的参数eta，第三个参数m_impl则是单子的一个实例，对应于将Free Monad求值后的单子m。这个函数返回单子值m a，在代码中是@TypeOf(m_impl).MbType(A) 这个类型。因为Zig语言中的Free Monad的操作指令列表是自下而上构造的，foldFree函数因此也是自下而上求值的。

当函数foldFree传入的self这个Free Monad是一个纯的值时，直接调用单子m的pure函数，返回单子m的纯的值。当传入的self时一个不纯的值时，首先将self中的纯的部分free_m[0]中的值pure_m应用到单子m的函数pure中，得到单子m 的纯的值acc_m。然后通过函数val_ctor_info.callValCtorFn以acc_m为参数调用lambda函数op_info.op_lam，构造出上一层的函子F 的类型为F (m a)的值f_acc_m。再应用到自然变换nat_impl的trans函数中，得到类型为m (m a)的值m_acc_m。最后调用单子m的join函数将类型为m (m a)的值m_acc_m拍扁为类型为m a的单一单子的值保存回acc_m中。如此不停的循环遍历完整个操作指令的列表，最终得到一个求值后的类型为m a的单子值保存到acc_m中并返回。

Zig语言实现的foldFree将Haskell中的递归实现改为对ArrayList数据类型的高效率的循环遍历，提升了不少性能。

到这里，我们基本上就把使用Zig实现Free Monad的过程讲清楚了。不过光有这些的话，Free Monad使用起来很不方便。我们就以Maybe函子构造出Free Monad的例子，来看一下要加些什么东西才能更方便使用。

Zig语言中已经内置了Maybe这个数据类型，就是?T 这个类型，对应了Haskell中的类型Maybe T。我写的Zig语言的函数式编程基础库中已经实现了Maybe这个数据类型的函子实例MaybeMonadImpl，直接使用就可以了。所以剩下的就是定义从底层的类型为A值构造出函子F 的类型为F A的值的lambda函数了，Maybe对应的这些lambda函数定义如下：

```c
fn MaybeCtorDefs(comptime A: type) type {
    return struct {
        pub const Nothing = NothingLam;
        pub const Just = JustLam;

        // Value constructor lambdas for Maybe
        const NothingLam = extern struct {
            lam_ctx: u64,
            const Self = @This();
            pub fn build() Self {
                return .{ .lam_ctx = 0 };
            }
            pub fn deinit(self: Self) void {
                _ = self;
            }
            pub fn call(self: Self) Maybe(A) {
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
            pub fn deinit(self: Self) void {
                _ = self;
            }
            pub fn call(self: Self, a: A) Maybe(A) {
                _ = self;
                return a;
            }
        };
    };
}
```

Maybe函子有两个值构造子Nothing和Just，因此也要有两个对应的构造F A的值的lambda函数，在上面的代码中就是NothingLam和JustLam这两个。因为保存在操作指令列表中的构造F A的值的lambda函数已经被擦除了类型，所以，在调用这两个lambda函数时需要恢复其类型。这是根据FOpInfo中的域成员op_e的值来恢复的，所以需要有类似下面的代码来做这件事：

```c
const lam = opinfo.op_lam;
const a = low_a;
const ctor_e = @as(CtorEnum, @enumFromInt(opinfo.op_e));
const fa = switch (ctor_e) {
    .Nothing => NothingLam.call(@bitCast(lam)),
    .Just => JustLam.call(@bitCast(lam), a)
}
```

这样才能够构造出类型为F A的值。但是如果这段代码需要手工写的话，一是工作量不小，二是有可能出错，编译期无法检查出错误而且出错后会导致奇怪的bug，难以查找bug的根源。所以我希望Zig语言能够帮我自动生成这段代码，这样就可以省去不少手写的代码了，另外还绝对不会出错。借助Zig语言强大的comptime的能力，我找到了一个方法来实现这个代码生成的功能。

限于篇幅，这里简短概要的介绍一下这个方法。

首先，用Zig标准库中提供的DeclEnum函数从MaybeCtorDefs(A)的结构体类型中得到枚举类型MaybeCtorEnum。会自动生成如下的MaybeCtorEnum的定义：

```c
const MaybeCtorEnum = enum {
    Nothing,
    Just,
};
```

然后，根据这个枚举类型依次从MaybeCtorDefs(A)的结构体类型中的构造F A的值的lambda函数的类型信息，将对应的枚举值和lambda函数的参数长度保存到元素类型为OpCtorInfo的数组中。

在上面的foldFree函数中，通过调用函数GetOpCtors获取到这个数组，然后根据op_info.op_e的值来检索这个数组得到当前使用的OpCtorInfo信息。再通过这个OpCtorInfo对应的callValCtorFn函数来调用构造F A的值的lambda函数op_info.op_lam。代码片段如下：

```c
                        const fm_op_ctors = GetOpCtors(F, MImpl.F(A));
                        const op_ctor_info = fm_op_ctors[op_info.op_e];
                        const f_acc_m = op_ctor_info.callValCtorFn(
                            op_info.op_lam,
                            @constCast(&[_]MImpl.F(A){acc_m}),
                        );
```

在函数callValCtorFn中，会使用如下的代码片段来恢复op_lam的类型并调用它，构造出F A类型的值。

```c
            switch (self.ctor_e) {
                inline else => |e| {
                    const OpLam = @field(OpDefs, @tagName(e));
                    const Args = std.meta.ArgsTuple(@TypeOf(OpLam.call));
                    var args: Args = undefined;
                    const args_fields = std.meta.fields(Args);
                    assert(args_fields.len - 1 == self.params_len);
                    // first parameter is lambda self
                    args[0] = @as(OpLam, @bitCast(op_lam));
                    comptime var i = 1;
                    inline while (i < @typeInfo(Args).Struct.fields.len) : (i += 1) {
                        args[i] = as[i - 1];
                    }
                    return @call(.auto, OpLam.call, args);                  
                },
            }
```

上面的代码中的在switch语句块中的inline else是Zig中非常有用的技巧，可以将运行时的self.ctor_e枚举值变为编译期的枚举值e。从而借助Zig语言的comptime的能力， 通过```@field(OpDefs, @tagName(e))``` 获取当前使用的OpCtorInfo对应的op_lam的类型，从而得到这个lambda函数的参数列表args。使用@bitCast恢复op_lam的类型，填好args中每一个参数中的值后，就可以调用到真实的构造F A的值的lambda函数了，得到F A的值。

于是，我们就自动得到了上面需要手工写的恢复构造F A的值的lambda函数op_lam的类型的代码。不管后续会增加多少函子F，也不管每个函子F 有多少值构造子，都不需要修改上面的自动恢复构造F A的值的lambda函数op_lam的类型的代码。一劳永逸的解决了问题。

我使用的这种自下而上构造的方式来实现的Free Monad，极大的提升了Haskell中原始设计的Free Monad的性能，也简化了代码的实现。使用Zig语言来实现一个函数式编程语言中才有的Free Monad的意义在于，现有的函数式编程语言的运行时都是比较厚重的，而且需要有GC来做自动内存管理。难以在性能较低、内存较小的硬件系统上使用。而Zig语言则是以C语言的替代者为目标，其运行时非常小，内存占用也很低，非常适合在这些硬件系统上使用。有了使用Zig语言实现的高性能的Free Monad，就可以在这些硬件系统上使用函数式编程所特有的这种灵活的设计了。另外，也给Zig这样的命令式语言带来了非常有用的函数式编程特性。

**参考链接：**

完整的代码实现在下面的[zig-cats](https://github.com/flyfish30/zig-cats)项目的[src/free_types.zig](https://github.com/flyfish30/zig-cats/blob/main/src/free_types.zig)文件中。

[zig-cats](https://github.com/flyfish30/zig-cats)
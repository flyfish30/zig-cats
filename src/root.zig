const std = @import("std");
const testing = std.testing;

// pub const pure = @import("pure.zig");

// module imports
const base = @import("base.zig");
const monoid = @import("monoid.zig");
const foldable = @import("foldable.zig");
const functor = @import("functor.zig");
const applicative = @import("applicative.zig");
const monad = @import("monad.zig");
const compose = @import("compose.zig");
const product = @import("product.zig");
const coproduct = @import("coproduct.zig");
const free_types = @import("free_types.zig");
const fixed_point = @import("fixed_point.zig");
const maybe = @import("maybe.zig");
const vector = @import("vector.zig");
const array_monad = @import("array_monad.zig");
const array_list_monad = @import("array_list_monad.zig");
const state = @import("state.zig");

// re-exports from base.zig
pub const typeId = base.typeId;
pub const ConstraitType = base.ConstraitType;
pub const TypeWithConstraits = base.TypeWithConstraits;
pub const isPureTypeClass = base.isPureTypeClass;
pub const TCtor = base.TCtor;
pub const GetPointerChild = base.GetPointerChild;
pub const MapFnInType = base.MapFnInType;
pub const MapFnRetType = base.MapFnRetType;
pub const MapLamInType = base.MapLamInType;
pub const MapLamRetType = base.MapLamRetType;
pub const MapFnToLamType = base.MapFnToLamType;
pub const mapFnToLam = base.mapFnToLam;
pub const AnyMapFn = base.AnyMapFn;
pub const ApplyFnInType = base.ApplyFnInType;
pub const ApplyFnRetType = base.ApplyFnRetType;
pub const ApplyLamInType = base.ApplyLamInType;
pub const ApplyLamRetType = base.ApplyLamRetType;
pub const MapFnKind = base.MapFnKind;
pub const isInplaceMap = base.isInplaceMap;
pub const isMapRef = base.isMapRef;
pub const FMapMode = base.FMapMode;
pub const RainbowColor = base.RainbowColor;
pub const identity = base.identity;
pub const getIdentityFn = base.getIdentityFn;
pub const getEffectIdentityFn = base.getEffectIdentityFn;
pub const IdentityLamType = base.IdentityLamType;
pub const getIdentityLam = base.getIdentityLam;
pub const EffectIdentityLamType = base.EffectIdentityLamType;
pub const getEffectIdentityLam = base.getEffectIdentityLam;
pub const pureFnToImpure = base.pureFnToImpure;
pub const EffectVal = base.EffectVal;
pub const AnyFnType = base.AnyFnType;
pub const AnyFnPtr = base.AnyFnPtr;
pub const AnyLamType = base.AnyLamType;
pub const getDefaultBaseCfg = base.getDefaultBaseCfg;
pub const ComposableLam = base.ComposableLam;
pub const LamWrapper = base.LamWrapper;
pub const anyLamFromLam = base.anyLamFromLam;
pub const ComposedFnType = base.ComposedFnType;
pub const comptimeCompose = base.comptimeCompose;
pub const ComposableFn = base.ComposableFn;
pub const ComposedLamType = base.ComposedLamType;
pub const composeLams = base.composeLams;
pub const ComposeManyLams = base.ComposeManyLams;
pub const isErrorUnionOrVal = base.isErrorUnionOrVal;
pub const castInplaceValue = base.castInplaceValue;
pub const defaultVal = base.defaultVal;
pub const getDefaultFn = base.getDefaultFn;
pub const Maybe = base.Maybe;
pub const Array = base.Array;
pub const Vector = base.Vector;
pub const FreeTFn = base.FreeTFn;
pub const getFreeNothing = base.getFreeNothing;
pub const freeNothing = base.freeNothing;
pub const tryStrongRef = base.tryStrongRef;
pub const copyOrCloneOrRef = base.copyOrCloneOrRef;
pub const getDeinitOrUnref = base.getDeinitOrUnref;
pub const tryStrongUnref = base.tryStrongUnref;
pub const deinitOrUnref = base.deinitOrUnref;
// re-exports that base.zig now forwards from base/util_types.zig
pub const Identity = base.Identity;
pub const Constant = base.Constant;
pub const AllBool = base.AllBool;
pub const AnyBool = base.AnyBool;
pub const SumNumb = base.SumNumb;
pub const ProductNumb = base.ProductNumb;

// re-exports from monoid.zig
pub const Monoid = monoid.Monoid;
pub const MonoidFromImpl = monoid.MonoidFromImpl;
pub const MonoidImplFromType = monoid.MonoidImplFromType;
pub const commonMconcat = monoid.commonMconcat;

// re-exports from foldable.zig
pub const FoldRetType = foldable.FoldRetType;
pub const Foldable = foldable.Foldable;
pub const FoldableFromImpl = foldable.FoldableFromImpl;
pub const FoldableImplFromTCtor = foldable.FoldableImplFromTCtor;
pub const commonFoldMap = foldable.commonFoldMap;
pub const commonFoldr = foldable.commonFoldr;

// re-exports from functor.zig
pub const MaybeFunctorImpl = functor.MaybeFunctorImpl;
pub const ArrayListFunctorImpl = functor.ArrayListFunctorImpl;
pub const FunctorFxTypes = functor.FunctorFxTypes;
pub const Functor = functor.Functor;
pub const FunctorFromImpl = functor.FunctorFromImpl;
pub const FunctorImplFromTCtor = functor.FunctorImplFromTCtor;
pub const NatGxTypes = functor.NatGxTypes;
pub const NatTrans = functor.NatTrans;
pub const MaybeToArrayNatImpl = functor.MaybeToArrayNatImpl;
pub const ArrayToMaybeNatImpl = functor.ArrayToMaybeNatImpl;
pub const MaybeToArrayListNatImpl = functor.MaybeToArrayListNatImpl;
pub const ArrayListToMaybeNatImpl = functor.ArrayListToMaybeNatImpl;

// re-exports from applicative.zig
pub const MaybeApplicativeImpl = applicative.MaybeApplicativeImpl;
pub const ArrayListApplicativeImpl = applicative.ArrayListApplicativeImpl;
pub const ApplicativeFxTypes = applicative.ApplicativeFxTypes;
pub const Applicative = applicative.Applicative;
pub const ApplicativeFromImpl = applicative.ApplicativeFromImpl;
pub const ApplicativeImplFromTCtor = applicative.ApplicativeImplFromTCtor;

// re-exports from monad.zig
pub const MonadFxTypes = monad.MonadFxTypes;
pub const Monad = monad.Monad;
pub const MonadFromImpl = monad.MonadFromImpl;
pub const MonadImplFromTCtor = monad.MonadImplFromTCtor;
pub const runDo = monad.runDo;

// re-exports from compose.zig
pub const ComposeFG = compose.ComposeFG;
pub const ComposeFunctorImpl = compose.ComposeFunctorImpl;
pub const ComposeApplicativeImpl = compose.ComposeApplicativeImpl;
pub const ComposeFunctor = compose.ComposeFunctor;
pub const ComposeApplicative = compose.ComposeApplicative;

// re-exports from product.zig
pub const ProductFG = product.ProductFG;
pub const getProductTypeTuple = product.getProductTypeTuple;
pub const ProductFunctorImpl = product.ProductFunctorImpl;
pub const ProductApplicativeImpl = product.ProductApplicativeImpl;
pub const ProductFunctor = product.ProductFunctor;
pub const ProductApplicative = product.ProductApplicative;

// re-exports from coproduct.zig
pub const CoproductFG = coproduct.CoproductFG;
pub const getCoproductTypeTuple = coproduct.getCoproductTypeTuple;
pub const CoproductFunctorImpl = coproduct.CoproductFunctorImpl;
pub const CoproductApplicativeImpl = coproduct.CoproductApplicativeImpl;
pub const CoproductFunctor = coproduct.CoproductFunctor;
pub const CoproductApplicative = coproduct.CoproductApplicative;

// re-exports from free_types.zig
pub const FOpEnumInt = free_types.FOpEnumInt;
pub const AnyOpLamCtxType = free_types.AnyOpLamCtxType;
pub const FOpInfo = free_types.FOpInfo;
pub const toAnyOpLam = free_types.toAnyOpLam;
pub const toSpecificOpLam = free_types.toSpecificOpLam;
pub const FreeMonad = free_types.FreeMonad;
pub const FreeM = free_types.FreeM;
pub const GetExistentialType = free_types.GetExistentialType;
pub const GetOpCtors = free_types.GetOpCtors;
pub const MaybeShowNatImpl = free_types.MaybeShowNatImpl;
pub const liftNothing = free_types.liftNothing;
pub const liftJust = free_types.liftJust;
pub const FreeMonadImpl = free_types.FreeMonadImpl;
pub const ListCfg = free_types.ListCfg;
pub const ListCtxCfg = free_types.ListCtxCfg;
pub const ListShowtNatImpl = free_types.ListShowtNatImpl;

// re-exports from fixed_point.zig
pub const Fix = fixed_point.Fix;
pub const Alg = fixed_point.Alg;
pub const cata = fixed_point.cata;

// re-exports from maybe.zig
pub const MaybeMonoidImpl = maybe.MaybeMonoidImpl;
pub const maybe_error = maybe.maybe_error;
pub const MaybeMonadImpl = maybe.MaybeMonadImpl;

// re-exports from vector.zig
pub const VectorMonoidImpl = vector.VectorMonoidImpl;

// re-exports from array_monad.zig
pub const ArrayMonoidImpl = array_monad.ArrayMonoidImpl;
pub const ArrayMonadImpl = array_monad.ArrayMonadImpl;
pub const ArrayFoldableImpl = array_monad.ArrayFoldableImpl;

// re-exports from array_list_monad.zig
pub const ArrayListMonoidImpl = array_list_monad.ArrayListMonoidImpl;
pub const ArrayListMonadImpl = array_list_monad.ArrayListMonadImpl;
pub const ArrayListFoldableImpl = array_list_monad.ArrayListFoldableImpl;

// re-exports from state.zig
pub const StateContext = state.StateContext;
pub const CloneStateSFn = state.CloneStateSFn;
pub const FreeStateSFn = state.FreeStateSFn;
pub const StateCtxCfg = state.StateCtxCfg;
pub const getDeinitCfg = state.getDeinitCfg;
pub const StateMonadImpl = state.StateMonadImpl;
pub const StateF = state.StateF;
pub const StateFA = state.StateFA;
pub const StateFFunctorImpl = state.StateFFunctorImpl;
pub const liftPutF = state.liftPutF;
pub const liftGetF = state.liftGetF;
pub const StateFToStateNatImpl = state.StateFToStateNatImpl;
pub const StateFShowNatImpl = state.StateFShowNatImpl;
pub const tell = state.tell;
pub const MWriterMonadImpl = state.MWriterMonadImpl;
pub const MWriterMaybe = state.MWriterMaybe;
pub const MWriterMaybeMonadImpl = state.MWriterMaybeMonadImpl;

test {
    std.testing.refAllDecls(@This());
}

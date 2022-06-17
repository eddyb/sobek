//! Builder abstraction allowing the use of overloaded operators and
//! inherent methods to build IR subgraphs more conveniently.

use crate::ir::{BitSize, Const, Cx, INode, IntOp, InternInCx, MemRef, Node, Type};

/// Newtype to simplify operator overloading by centralizing blanket impls.
///
/// In general, `impl<T: Foo, U: Bar> Add<U> for T` doesn't pass coherence even
/// when `Foo`/`Bar` are only implemented for a fixed set of type constructors,
/// so instead one of these two approaches is needed:
/// * expand the `impl` for every shape of `T`/`U` that it could possibly fit,
///   as to not need the `Foo`/`Bar` bounds, at the cost of needing many `impl`s
/// * use `impl<T: Foo, U: Bar> Add<U> for Builder<T>` instead, at the const of
///   additional wrapping/unwrapping (which may be abstracted away sometimes)
///
/// The second approach is used here, hence this newtype.
#[derive(Copy, Clone)]
pub struct Builder<T>(T);

impl<T> InternInCx for Builder<T>
where
    Self: Build<Cx>,
{
    type Interned = INode;
    fn intern_in_cx(self, cx: &Cx) -> INode {
        Cx::built_to_interned(cx, self.build(cx))
    }
}

pub trait Build<C: BuildCx>: Sized {
    fn build(self, cx: &C) -> C::Built;
}

pub trait BuildCx: Sized {
    type Built: Copy;
    fn built_from_const(c: Const) -> Self::Built;
    fn intern_to_built(&self, node: Node) -> Self::Built;
    fn built_to_interned(&self, built: Self::Built) -> INode;
    fn built_ty(&self, built: Self::Built) -> Type;
    fn built_as_const(&self, built: Self::Built) -> Option<Const>;
}

impl<C: BuildCx> Build<C> for Const {
    #[inline(always)]
    fn build(self, _cx: &C) -> C::Built {
        C::built_from_const(self)
    }
}

impl BuildCx for Cx {
    type Built = Result<Const, INode>;

    #[inline(always)]
    fn built_from_const(c: Const) -> Self::Built {
        Ok(c)
    }

    #[inline]
    fn intern_to_built(&self, node: Node) -> Self::Built {
        Err(self.a(node))
    }

    #[inline]
    fn built_to_interned(&self, built: Self::Built) -> INode {
        match built {
            Ok(c) => self.a(Node::Const(c)),
            Err(x) => x,
        }
    }

    #[inline]
    fn built_ty(&self, built: Self::Built) -> Type {
        match built {
            Ok(c) => Node::Const(c).ty(self),
            Err(x) => self[x].ty(self),
        }
    }

    #[inline]
    fn built_as_const(&self, built: Self::Built) -> Option<Const> {
        match built {
            Ok(c) => Some(c),
            Err(x) => self[x].as_const(),
        }
    }
}

impl Build<Cx> for INode {
    #[inline(always)]
    fn build(self, _cx: &Cx) -> <Cx as BuildCx>::Built {
        Err(self)
    }
}

// HACK(eddyb) rather than declaring everything with configurable macros, these
// "higher-order macros" effectively describe lists that can be then "iterated"
// (they invoke the macro name `$m` they get passed in, for each list item).
macro_rules! with_binops {
    ($m:ident!($($prefix:tt)*)) => {
        // These map to a single `Node::Int(IntOp::Foo, ...)` each.
        // (`[failible]` is used to indicate `Const` cannot be supported because
        // for some values the operation can fail to evaluate, e.g. `x / 0`)
        $m!($($prefix)* Add::add = IntOp::Add);
        $m!($($prefix)* Mul::mul = IntOp::Mul);
        $m!($($prefix)* [failible] DivS::div_s = IntOp::DivS);
        $m!($($prefix)* [failible] DivU::div_u = IntOp::DivU);
        $m!($($prefix)* [failible] RemS::rem_s = IntOp::RemS);
        $m!($($prefix)* [failible] RemU::rem_u = IntOp::RemU);
        $m!($($prefix)* CmpEq::cmp_eq = IntOp::Eq);
        $m!($($prefix)* CmpLtS::cmp_lt_s = IntOp::LtS);
        $m!($($prefix)* CmpLtU::cmp_lt_u = IntOp::LtU);
        $m!($($prefix)* BitAnd::bitand = IntOp::And);
        $m!($($prefix)* BitOr::bitor = IntOp::Or);
        $m!($($prefix)* BitXor::bitxor = IntOp::Xor);
        $m!($($prefix)* Shl::shl = IntOp::Shl);
        $m!($($prefix)* ShrS::shr_s = IntOp::ShrS);
        $m!($($prefix)* ShrU::shr_u = IntOp::ShrU);

        // These are more "artificial".
        $m!($($prefix)* Sub::sub);
        // FIXME(eddyb) these names are a bit too short maybe?
        $m!($($prefix)* Rol::rol);
        $m!($($prefix)* Ror::ror);
    };
}
macro_rules! with_binops_needing_inherent_proxy {
    ($m:ident!($($prefix:tt)*)) => {
        // These aren't actually part of the Rust language, and need inherent methods.
        $m!($($prefix)* DivS::div_s);
        $m!($($prefix)* DivU::div_u);
        $m!($($prefix)* RemS::rem_s);
        $m!($($prefix)* RemU::rem_u);
        $m!($($prefix)* CmpEq::cmp_eq);
        $m!($($prefix)* CmpLtS::cmp_lt_s);
        $m!($($prefix)* CmpLtU::cmp_lt_u);
        $m!($($prefix)* ShrS::shr_s);
        $m!($($prefix)* ShrU::shr_u);
        $m!($($prefix)* Rol::rol);
        $m!($($prefix)* Ror::ror);
    };
}
macro_rules! with_binops_shiftlike {
    ($m:ident!($($prefix:tt)*)) => {
        // These are "shift-like", i.e. their RHS is a bit count.
        $m!($($prefix)* Shl::shl);
        $m!($($prefix)* ShrS::shr_s);
        $m!($($prefix)* ShrU::shr_u);
        $m!($($prefix)* Rol::rol);
        $m!($($prefix)* Ror::ror);
    };
}
macro_rules! with_unops {
    ($m:ident!($($prefix:tt)*)) => {
        $m!($($prefix)* Neg::neg);
        $m!($($prefix)* Not::not);
    }
}
macro_rules! with_cast_ops {
    ($m:ident!($($prefix:tt)*)) => {
        $m!($($prefix)* Trunc => trunc);
        $m!($($prefix)* Sext => sext);
        $m!($($prefix)* Zext => zext);
    };
}

/// Marker types used in parameterizing `Builder` (to specify an operation).
mod tag {
    use crate::ir::IntOp;

    macro_rules! decl_binop {
        ($([failible])? $Trait:ident :: $method:ident $(= $int_op:expr)?) => {
            pub struct $Trait;
            $(impl Into<IntOp> for $Trait {
                #[inline(always)]
                fn into(self) -> IntOp {
                    $int_op
                }
            })?
        };
    }

    macro_rules! decl_unop {
        ($Trait:ident :: $method:ident) => {
            pub struct $Trait;
        };
    }
    macro_rules! decl_cast_op {
        ($Op:ident => $method:ident) => {
            pub struct $Op;
        };
    }
    with_binops!(decl_binop!());
    with_unops!(decl_unop!());
    with_cast_ops!(decl_cast_op!());

    // HACK(eddyb) manual for now (not macro-integrated).
    pub struct Load;
    pub struct Store;
}

/// `std::ops` traits, and additional ones, all used for multi-dispatch.
mod ops {
    pub use std::ops::{Add, BitAnd, BitOr, BitXor, Mul, Neg, Not, Shl, Sub};

    macro_rules! decl_faux_binop {
        ($Trait:ident :: $method:ident) => {
            pub trait $Trait<Other = Self> {
                type Output;
                fn $method(self, other: Other) -> Self::Output;
            }
        };
    }
    with_binops_needing_inherent_proxy!(decl_faux_binop!());
}

/// Marker trait used by any `Builder`-producing operators/methods, for params
/// not limited by coherence (e.g. the RHS type of `std::ops` binops - the LHS
/// in that case has to be a local type like `Builder<_>` / `INode`, instead).
pub trait OpInput {}

/// Like `OpInput`, but excluding `Const`, to avoid covering the case where both
/// operands are `Const` (which is separately implemented to return `Const`).
pub trait OpInputNoConst {}

macro_rules! impl_op_input {
    (
        OpInputTypes {
            $($In:ident $(<$($InG:ident),+>)?),+ $(,)?
        }
        OpInputNoConstTypes {
            $($InNoConst:ident $(<$($InNoConstG:ident),+>)?),+ $(,)?
        }
    ) => {
        $(impl<$($($InG,)+)?> OpInput for $In<$($($InG,)+)?> {})+
        $(impl<$($($InNoConstG,)+)?> OpInputNoConst for $InNoConst<$($($InNoConstG,)+)?> {})+
    };
}

macro_rules! impl_binop {
    (
        OpInputTypes {
            $($In:ident $(<$($InG:ident),+>)?),+ $(,)?
        }
        OpInputNoConstTypes {
            $($InNoConst:ident $(<$($InNoConstG:ident),+>)?),+ $(,)?
        }

        $([failible])? $Trait:ident :: $method:ident $(= $int_op:expr)?
    ) => {
        // All `(any OpInput, any OpInput)` combinations except `(Const, _)`.
        $(impl<$($($InNoConstG,)+)? Other: OpInput>
            ops::$Trait<Other> for $InNoConst<$($($InNoConstG,)+)?>
        {
            type Output = Builder<(tag::$Trait, Self, Other)>;
            #[inline(always)]
            fn $method(self, other: Other) -> Self::Output {
                Builder((tag::$Trait, self, other))
            }
        })+

        // All `(Const, any OpInput)` combinations except `(Const, Const)`.
        impl<Other: OpInputNoConst> ops::$Trait<Other> for Const {
            type Output = Builder<(tag::$Trait, Self, Other)>;
            #[inline(always)]
            fn $method(self, other: Other) -> Self::Output {
                Builder((tag::$Trait, self, other))
            }
        }

        // The remaining `(Const, Const)` combination of operands is handled
        // elsewhere (see `impl_const_binop`).
    };
}
macro_rules! impl_binop_inherent_proxy {
    (
        OpInputTypes {
            $($In:ident $(<$($InG:ident),+>)?),+ $(,)?
        }
        OpInputNoConstTypes {
            $($InNoConst:ident $(<$($InNoConstG:ident),+>)?),+ $(,)?
        }

        $Trait:ident :: $method:ident
    ) => {
        $(impl<$($($InG,)+)?> $In<$($($InG,)+)?> {
            #[inline(always)]
            pub fn $method<Other>(
                self,
                other: Other,
            ) -> <Self as ops::$Trait<Other>>::Output
                where Self: ops::$Trait<Other>
            {
                ops::$Trait::$method(self, other)
            }
        })+
    };
}
macro_rules! impl_binop_shiftlike {
    (
        OpInputTypes {
            $($In:ident $(<$($InG:ident),+>)?),+ $(,)?
        }
        OpInputNoConstTypes {
            $($InNoConst:ident $(<$($InNoConstG:ident),+>)?),+ $(,)?
        }

        $Trait:ident :: $method:ident
    ) => {
        // FIXME(eddyb) more than one such impl makes integer literal inference
        // ambiguous, but it also can't be generic because it'd conflict.
        $(impl<$($($InG,)+)?> ops::$Trait<u32> for $In<$($($InG,)+)?>
            where Self: ops::$Trait<Const>
        {
            type Output = <Self as ops::$Trait<Const>>::Output;
            #[inline(always)]
            fn $method(self, amount: u32) -> Self::Output {
                ops::$Trait::$method(self, Const::new(BitSize::B8, amount as u64))
            }
        })+
    };
}
macro_rules! impl_unop {
    (
        OpInputTypes {
            $($In:ident $(<$($InG:ident),+>)?),+ $(,)?
        }
        OpInputNoConstTypes {
            $($InNoConst:ident $(<$($InNoConstG:ident),+>)?),+ $(,)?
        }

        $Trait:ident :: $method:ident
    ) => {
        $(impl<$($($InG,)+)?> ops::$Trait for $In<$($($InG,)+)?> {
            type Output = Builder<(tag::$Trait, Self)>;
            #[inline(always)]
            fn $method(self) -> Self::Output {
                Builder((tag::$Trait, self))
            }
        })+
    };
}
macro_rules! impl_cast_op {
    (
        OpInputTypes {
            $($In:ident $(<$($InG:ident),+>)?),+ $(,)?
        }
        OpInputNoConstTypes {
            $($InNoConst:ident $(<$($InNoConstG:ident),+>)?),+ $(,)?
        }

        $Op:ident => $method:ident
    ) => {
        $(impl<$($($InNoConstG,)+)?> $InNoConst<$($($InNoConstG,)+)?> {
            #[inline(always)]
            pub fn $method(self, size: BitSize) -> Builder<(tag::$Op, BitSize, Self)> {
                Builder((tag::$Op, size, self))
            }
        })+

        impl<C: BuildCx, T: Build<C>> Build<C> for Builder<(tag::$Op, BitSize, T)> {
            #[inline]
            fn build(self, cx: &C) -> C::Built {
                let Builder((tag::$Op, size, x)) = self;
                let x = x.build(cx);

                let x_size = cx.built_ty(x).bit_size().unwrap();

                // FIXME(eddyb) this duplicates some `Node::normalize_for_interning` simplification.

                // Simplify noops.
                if size == x_size {
                    return x;
                }

                if let Some(c) = cx.built_as_const(x) {
                    return C::built_from_const(c.$method(size));
                }

                cx.intern_to_built(Node::$Op(size, cx.built_to_interned(x)))
            }
        }
    };
}
macro_rules! impl_all {
    ($($globals:tt)*) => {
        impl_op_input!($($globals)*);
        with_binops!(impl_binop!($($globals)*));
        with_binops_needing_inherent_proxy!(impl_binop_inherent_proxy!($($globals)*));
        with_binops_shiftlike!(impl_binop_shiftlike!($($globals)*));
        with_unops!(impl_unop!($($globals)*));
        with_cast_ops!(impl_cast_op!($($globals)*));
    }
}
impl_all! {
    OpInputTypes {
        Builder<T>,
        INode,
        Const,
    }
    OpInputNoConstTypes {
        Builder<T>,
        INode,
    }
}

impl<C: BuildCx, O: Into<IntOp>, A: Build<C>, B: Build<C>> Build<C> for Builder<(O, A, B)> {
    #[inline]
    fn build(self, cx: &C) -> C::Built {
        let Builder((op, a, b)) = self;
        let op = op.into();
        let (a, b) = (a.build(cx), b.build(cx));

        // FIXME(eddyb) this duplicates some `Node::normalize_for_interning` simplification.
        let c_a = cx.built_as_const(a);
        let c_b = cx.built_as_const(b);
        if let Some(r) = op.simplify(c_a.ok_or(a), c_b.ok_or(b)) {
            return r.map(C::built_from_const).unwrap_or_else(|x| x);
        }

        let size = cx.built_ty(a).bit_size().unwrap();

        cx.intern_to_built(Node::Int(
            op,
            size,
            cx.built_to_interned(a),
            cx.built_to_interned(b),
        ))
    }
}

// HACK(eddyb) this allows custom impls to reinput `C::Built` into operators.
#[derive(Copy, Clone)]
struct FromBuilt;
impl<C: BuildCx> Build<C> for Builder<(FromBuilt, C::Built)> {
    #[inline(always)]
    fn build(self, _cx: &C) -> C::Built {
        let Builder((FromBuilt, x)) = self;
        x
    }
}
fn from_built<T>(x: T) -> Builder<(FromBuilt, T)> {
    Builder((FromBuilt, x))
}

// FIXME(eddyb) this could theoretically be evaluated when `Sub::sub` gets called,
// and have it return `(Add, A, (Neg, B))` then.
impl<C: BuildCx, A: Build<C>, B: Build<C>> Build<C> for Builder<(tag::Sub, A, B)> {
    #[inline]
    fn build(self, cx: &C) -> C::Built {
        let Builder((tag::Sub, a, b)) = self;
        let (a, b) = (a.build(cx), b.build(cx));

        let (a, b) = (from_built(a), from_built(b));
        (a + (-b)).build(cx)
    }
}

impl<C: BuildCx, A: Build<C>, B: Build<C>> Build<C> for Builder<(tag::Rol, A, B)> {
    #[inline]
    fn build(self, cx: &C) -> C::Built {
        let Builder((tag::Rol, v, n)) = self;
        let (v, n) = (v.build(cx), n.build(cx));

        let v_size = cx.built_ty(v).bit_size().unwrap();
        let n_size = cx.built_ty(n).bit_size().unwrap();

        let (v, n) = (from_built(v), from_built(n));
        ((v << n) | v.shr_u(Const::new(n_size, v_size.bits() as u64) - n)).build(cx)
    }
}

impl<C: BuildCx, A: Build<C>, B: Build<C>> Build<C> for Builder<(tag::Ror, A, B)> {
    #[inline]
    fn build(self, cx: &C) -> C::Built {
        let Builder((tag::Ror, v, n)) = self;
        let (v, n) = (v.build(cx), n.build(cx));

        let v_size = cx.built_ty(v).bit_size().unwrap();
        let n_size = cx.built_ty(n).bit_size().unwrap();

        let (v, n) = (from_built(v), from_built(n));
        (v.shr_u(n) | (v << (Const::new(n_size, v_size.bits() as u64) - n))).build(cx)
    }
}

impl<C: BuildCx, T: Build<C>> Build<C> for Builder<(tag::Neg, T)> {
    #[inline]
    fn build(self, cx: &C) -> C::Built {
        let Builder((tag::Neg, x)) = self;
        let x = x.build(cx);

        let size = cx.built_ty(x).bit_size().unwrap();
        let minus_1 = Const::new(size, size.mask());

        let x = from_built(x);
        (x * minus_1).build(cx)
    }
}

impl<C: BuildCx, T: Build<C>> Build<C> for Builder<(tag::Not, T)> {
    #[inline]
    fn build(self, cx: &C) -> C::Built {
        let Builder((tag::Not, x)) = self;
        let x = x.build(cx);

        let size = cx.built_ty(x).bit_size().unwrap();
        let all_ones = Const::new(size, size.mask());

        let x = from_built(x);
        (x ^ all_ones).build(cx)
    }
}

impl<A: OpInput> MemRef<A> {
    #[inline(always)]
    pub fn load(self) -> Builder<(tag::Load, Self)> {
        Builder((tag::Load, self))
    }

    #[inline(always)]
    pub fn store<V: OpInput>(self, v: V) -> Builder<(tag::Store, Self, V)> {
        Builder((tag::Store, self, v))
    }
}

impl<A: Build<Cx>> Build<Cx> for Builder<(tag::Load, MemRef<A>)> {
    #[inline]
    fn build(self, cx: &Cx) -> <Cx as BuildCx>::Built {
        let Builder((tag::Load, r)) = self;
        let r = r.map_addr(|a| a.build(cx));

        cx.intern_to_built(Node::Load(r.map_addr(|a| cx.built_to_interned(a))))
    }
}
impl<A: Build<Cx>, V: Build<Cx>> Build<Cx> for Builder<(tag::Store, MemRef<A>, V)> {
    #[inline]
    fn build(self, cx: &Cx) -> <Cx as BuildCx>::Built {
        let Builder((tag::Store, r, v)) = self;
        let (r, v) = (r.map_addr(|a| a.build(cx)), v.build(cx));

        cx.intern_to_built(Node::Store(
            r.map_addr(|a| cx.built_to_interned(a)),
            cx.built_to_interned(v),
        ))
    }
}

// `Const` overloaded ops.

/// `BuildCx` implementor that only supports `Const`s.
struct ConstCx;

impl BuildCx for ConstCx {
    type Built = Const;

    #[inline(always)]
    fn built_from_const(c: Const) -> Self::Built {
        c
    }

    #[inline]
    #[track_caller]
    fn intern_to_built(&self, _: Node) -> Self::Built {
        unreachable!("`Const` operator overloading shouldn't need interning")
    }

    #[inline]
    #[track_caller]
    fn built_to_interned(&self, _: Self::Built) -> INode {
        unreachable!("`Const` operator overloading shouldn't need interning")
    }

    #[inline(always)]
    fn built_ty(&self, built: Self::Built) -> Type {
        Type::Bits(built.size)
    }

    #[inline(always)]
    fn built_as_const(&self, built: Self::Built) -> Option<Const> {
        Some(built)
    }
}

macro_rules! impl_const_binop {
    ($Trait:ident :: $method:ident $(= $int_op:expr)?) => {
        impl ops::$Trait for Const {
            type Output = Const;
            #[inline]
            fn $method(self, other: Const) -> Const {
                Builder((tag::$Trait, self, other)).build(&ConstCx)
            }
        }
    };
    ([failible] $Trait:ident :: $method:ident $(= $int_op:expr)?) => {
        // Ignore `{Div,Rem}{U,S}`, as they can fail for specific values,
        // e.g. `x / 0`.
    };
}
with_binops!(impl_const_binop!());

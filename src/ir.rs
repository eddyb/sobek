use scoped_tls::scoped_thread_local;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::ops::{Index, RangeTo};

pub use self::store::*;
mod store {
    use super::*;

    use elsa::FrozenVec;
    use std::cell::RefCell;
    use std::cmp::Ordering;
    use std::collections::hash_map::Entry;
    use std::collections::HashMap;
    use std::convert::TryInto;
    use std::hash::{Hash, Hasher};

    pub struct Use<T> {
        idx: u32,
        _marker: PhantomData<T>,
    }

    // HACK(eddyb) work around `#[derive]` adding bounds on `T`.
    impl<T> Copy for Use<T> {}
    impl<T> Clone for Use<T> {
        fn clone(&self) -> Self {
            *self
        }
    }

    impl<T> PartialEq for Use<T> {
        fn eq(&self, other: &Self) -> bool {
            self.idx == other.idx
        }
    }
    impl<T> Eq for Use<T> {}

    impl<T> PartialOrd for Use<T> {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.idx.partial_cmp(&other.idx)
        }
    }
    impl<T> Ord for Use<T> {
        fn cmp(&self, other: &Self) -> Ordering {
            self.idx.cmp(&other.idx)
        }
    }

    impl<T> Hash for Use<T> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.idx.hash(state);
        }
    }

    // FIXME(eddyb) rename Store to Interner, and adjust adjacent terminology.

    pub struct Store<T> {
        // FIXME(Manishearth/elsa#6) switch to `FrozenIndexSet` when available.
        map: RefCell<HashMap<T, Use<T>>>,
        vec: FrozenVec<Box<T>>,
    }

    #[derive(Default)]
    pub(super) struct Stores {
        node: Store<Node>,
    }

    impl<T: Eq + Hash> Default for Store<T> {
        fn default() -> Self {
            Store {
                map: Default::default(),
                vec: Default::default(),
            }
        }
    }

    impl<T> Index<Use<T>> for Store<T> {
        type Output = T;
        fn index(&self, u: Use<T>) -> &T {
            &self.vec[u.idx as usize]
        }
    }

    impl<T: Copy + Eq + Hash> Store<T> {
        fn alloc(&self, x: T) -> Use<T> {
            match self.map.borrow_mut().entry(x) {
                Entry::Occupied(entry) => *entry.get(),
                Entry::Vacant(entry) => {
                    let next = self.vec.len().try_into().unwrap();
                    self.vec.push(Box::new(x));
                    *entry.insert(Use {
                        idx: next,
                        _marker: PhantomData,
                    })
                }
            }
        }
    }

    impl Cx {
        pub fn new(platform: impl Platform + 'static) -> Self {
            let stores = Stores::default();

            let default = State {
                mem: stores.node.alloc(Node::InMem),
                regs: vec![],
            };

            let mut cx = Cx {
                stores,
                platform: Box::new(platform),
                default,
            };

            cx.default.regs = cx.platform.isa().default_regs(&cx);

            cx
        }
    }

    pub trait AllocIn: Sized {
        type Interned;
        fn alloc_in(self, cx: &Cx) -> Self::Interned;
    }

    // FIXME(eddyb) is this sort of thing even needed anymore?
    impl<T: AllocIn<Interned = Use<T>>, F: FnOnce(&Cx) -> T> AllocIn for F {
        type Interned = Use<T>;
        fn alloc_in(self, cx: &Cx) -> Use<T> {
            self(cx).alloc_in(cx)
        }
    }

    impl Cx {
        pub fn a<T: AllocIn>(&self, x: T) -> T::Interned {
            x.alloc_in(self)
        }
    }

    impl AllocIn for Node {
        type Interned = Use<Self>;
        fn alloc_in(self, cx: &Cx) -> Use<Self> {
            match self.normalize(cx) {
                Ok(x) => cx.stores.node.alloc(x),
                Err(u) => u,
            }
        }
    }

    impl Index<Use<Node>> for Cx {
        type Output = Node;
        fn index(&self, node: Use<Node>) -> &Self::Output {
            self.stores.node.index(node)
        }
    }

    impl fmt::Debug for Use<Node> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            let local = if DBG_LOCALS.is_set() {
                DBG_LOCALS.with(|locals| locals.get(self).copied())
            } else {
                None
            };
            match local {
                Some((prefix, i)) => write!(f, "{}{}", prefix, i),
                None => {
                    if DBG_CX.is_set() {
                        DBG_CX.with(|cx| write!(f, "{:?}", &cx[*self]))
                    } else {
                        write!(f, "node#{:x}", self.idx)
                    }
                }
            }
        }
    }
}

scoped_thread_local!(static DBG_CX: Cx);
scoped_thread_local!(static DBG_LOCALS: HashMap<Use<Node>, (&'static str, usize)>);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BitSize {
    B1,
    B8,
    B16,
    B32,
    B64,
}

impl BitSize {
    pub fn bits(self) -> u8 {
        match self {
            BitSize::B1 => 1,
            BitSize::B8 => 8,
            BitSize::B16 => 16,
            BitSize::B32 => 32,
            BitSize::B64 => 64,
        }
    }

    pub fn bits_subscript(self) -> &'static str {
        match self {
            BitSize::B1 => "₁",
            BitSize::B8 => "₈",
            BitSize::B16 => "₁₆",
            BitSize::B32 => "₃₂",
            BitSize::B64 => "₆₄",
        }
    }

    fn mask(self) -> u64 {
        !0 >> (64 - self.bits())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Const {
    pub size: BitSize,
    bits: u64,
}

impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (a, b, c, d) = (
            (self.bits >> 48) as u16,
            (self.bits >> 32) as u16,
            (self.bits >> 16) as u16,
            self.bits as u16,
        );
        if a != 0 {
            write!(f, "0x{:04x}_{:04x}_{:04x}_{:04x}", a, b, c, d)
        } else if b != 0 {
            write!(f, "0x{:04x}_{:04x}_{:04x}", b, c, d)
        } else if c != 0 {
            write!(f, "0x{:04x}_{:04x}", c, d)
        } else if d > 9 {
            if self.size >= BitSize::B16 {
                write!(f, "0x{:04x}", d)
            } else {
                write!(f, "0x{:02x}", d)
            }
        } else {
            write!(f, "{}", d)
        }
    }
}

impl AllocIn for Const {
    type Interned = Use<Node>;
    fn alloc_in(self, cx: &Cx) -> Use<Node> {
        cx.a(Node::Const(self))
    }
}

impl From<bool> for Const {
    fn from(b: bool) -> Self {
        Const::new(BitSize::B1, b as u64)
    }
}

impl Const {
    pub fn new(size: BitSize, bits: u64) -> Self {
        assert!(
            bits == (bits & size.mask()),
            "Const::new({:?}, 0x{:x}): value does not fit",
            size,
            bits
        );

        Const { size, bits }
    }

    pub fn as_i8(&self) -> i8 {
        self.as_i64() as i8
    }

    pub fn as_u8(&self) -> u8 {
        self.as_u64() as u8
    }

    pub fn as_i16(&self) -> i16 {
        self.as_i64() as i16
    }

    pub fn as_u16(&self) -> u16 {
        self.as_u64() as u16
    }

    pub fn as_i32(&self) -> i32 {
        self.as_i64() as i32
    }

    pub fn as_u32(&self) -> u32 {
        self.as_u64() as u32
    }

    pub fn as_i64(&self) -> i64 {
        let n = 64 - self.size.bits();
        (self.bits as i64) << n >> n
    }

    pub fn as_u64(&self) -> u64 {
        let n = 64 - self.size.bits();
        self.bits << n >> n
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntOp {
    Add,
    Mul,
    DivS,
    DivU,
    RemS,
    RemU,

    Eq,
    LtS,
    LtU,

    And,
    Or,
    Xor,

    Shl,
    ShrS,
    ShrU,
}

impl IntOp {
    pub fn as_str(self) -> &'static str {
        match self {
            IntOp::Add => "+",
            IntOp::Mul => "*",
            IntOp::DivS => "/ₛ",
            IntOp::DivU => "/ᵤ",
            IntOp::RemS => "%ₛ",
            IntOp::RemU => "%ᵤ",

            IntOp::Eq => "==",
            IntOp::LtS => "<ₛ",
            IntOp::LtU => "<ᵤ",

            IntOp::And => "&",
            IntOp::Or => "|",
            IntOp::Xor => "^",

            IntOp::Shl => "<<",
            IntOp::ShrS => ">>ₛ",
            IntOp::ShrU => ">>ᵤ",
        }
    }

    pub fn eval(self, a: Const, b: Const) -> Option<Const> {
        let size = match self {
            IntOp::Eq | IntOp::LtS | IntOp::LtU => BitSize::B1,
            _ => a.size,
        };
        let is_shift = match self {
            IntOp::Shl | IntOp::ShrU | IntOp::ShrS => true,
            _ => false,
        };
        let is_signed = match self {
            IntOp::DivS | IntOp::RemS | IntOp::LtS | IntOp::ShrS => true,
            _ => false,
        };
        if !is_shift {
            assert_eq!(a.size, b.size);
        }
        let a = if is_signed {
            a.as_i64() as u64
        } else {
            a.as_u64()
        };
        let b = if is_shift {
            // Mask the shift amount so that the number of bits shifted is always
            // smaller than the number of total bits in the value being shifted.
            (b.as_u8() & (size.bits() - 1)) as u64
        } else if is_signed {
            b.as_i64() as u64
        } else {
            b.as_u64()
        };

        let r = match self {
            IntOp::Add => a.wrapping_add(b),
            IntOp::Mul => a.wrapping_mul(b),
            IntOp::DivS => (a as i64).checked_div(b as i64)? as u64,
            IntOp::DivU => a.checked_div(b)?,
            IntOp::RemS => (a as i64).checked_rem(b as i64)? as u64,
            IntOp::RemU => a.checked_rem(b)?,

            IntOp::Eq => (a == b) as u64,
            IntOp::LtS => ((a as i64) < (b as i64)) as u64,
            IntOp::LtU => (a < b) as u64,

            IntOp::And => a & b,
            IntOp::Or => a | b,
            IntOp::Xor => a ^ b,

            IntOp::Shl => a << b,
            IntOp::ShrS => ((a as i64) >> b) as u64,
            IntOp::ShrU => a >> b,
        };
        Some(Const::new(size, r & size.mask()))
    }

    pub fn simplify<T: Copy>(
        self,
        a: Result<Const, T>,
        b: Result<Const, T>,
    ) -> Option<Result<Const, T>> {
        if let (Ok(a), Ok(b)) = (a, b) {
            return Some(Ok(self.eval(a, b)?));
        }

        // Symmetric ops.
        match (a, b) {
            (Ok(x), Err(other)) | (Err(other), Ok(x)) => match (self, x.as_i64()) {
                (IntOp::Add, 0)
                | (IntOp::Mul, 1)
                | (IntOp::And, -1)
                | (IntOp::Or, 0)
                | (IntOp::Xor, 0) => return Some(Err(other)),

                (IntOp::Mul, 0) | (IntOp::And, 0) | (IntOp::Or, -1) => return Some(Ok(x)),

                _ => {}
            },
            _ => {}
        }

        // Asymmetric ops.
        match (a, b) {
            (Ok(a), Err(_)) => match (a.as_i64(), self) {
                (0, IntOp::DivS)
                | (0, IntOp::DivU)
                | (0, IntOp::RemS)
                | (0, IntOp::RemU)
                | (0, IntOp::Shl)
                | (0, IntOp::ShrS)
                | (-1, IntOp::ShrS)
                | (0, IntOp::ShrU) => return Some(Ok(a)),

                (-1, IntOp::LtU) => return Some(Ok(Const::from(true))),

                _ => {}
            },

            (Err(a), Ok(b)) => match (self, b.as_i64()) {
                (IntOp::DivS, 1)
                | (IntOp::DivU, 1)
                | (IntOp::Shl, 0)
                | (IntOp::ShrS, 0)
                | (IntOp::ShrU, 0) => return Some(Err(a)),

                (IntOp::LtU, 0) => return Some(Ok(Const::from(false))),

                _ => {}
            },

            _ => {}
        }

        if self == IntOp::LtS {
            match (a, b) {
                // FIXME(eddyb) move these (max & min) values somewhere more sensible.
                (Ok(a), Err(_)) if a.bits == ((1 << (a.size.bits() - 1)) - 1) => {
                    return Some(Ok(Const::from(true)));
                }

                (Err(_), Ok(b)) if b.bits == 1 << (b.size.bits() - 1) => {
                    return Some(Ok(Const::from(false)));
                }

                _ => {}
            }
        }

        None
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Reg {
    pub index: usize,
    pub size: BitSize,
    pub name: &'static str,
}

impl fmt::Debug for Reg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Bits(BitSize),
    Mem,
}

impl Type {
    pub fn bit_size(self) -> Result<BitSize, Type> {
        match self {
            Type::Bits(size) => Ok(size),
            _ => Err(self),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemSize {
    M8,
    M16,
    M32,
    M64,
}

impl Into<BitSize> for MemSize {
    fn into(self) -> BitSize {
        match self {
            MemSize::M8 => BitSize::B8,
            MemSize::M16 => BitSize::B16,
            MemSize::M32 => BitSize::B32,
            MemSize::M64 => BitSize::B64,
        }
    }
}

impl MemSize {
    pub fn bits(self) -> u8 {
        match self {
            MemSize::M8 => 8,
            MemSize::M16 => 16,
            MemSize::M32 => 32,
            MemSize::M64 => 64,
        }
    }

    pub fn bits_subscript(self) -> &'static str {
        match self {
            MemSize::M8 => "₈",
            MemSize::M16 => "₁₆",
            MemSize::M32 => "₃₂",
            MemSize::M64 => "₆₄",
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct MemRef {
    pub mem: Use<Node>,
    pub addr: Use<Node>,
    pub size: MemSize,
}

impl fmt::Debug for MemRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{:?}[{:?}]{}",
            self.mem,
            self.addr,
            self.size.bits_subscript()
        )
    }
}

impl MemRef {
    pub fn subst(self, cx: &Cx, base: &State) -> Self {
        MemRef {
            mem: self.mem.subst(cx, base),
            addr: self.addr.subst(cx, base),
            size: self.size,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Node {
    // Bits nodes.
    InReg(Reg),

    Const(Const),
    Int(IntOp, BitSize, Use<Node>, Use<Node>),
    Trunc(BitSize, Use<Node>),
    Sext(BitSize, Use<Node>),
    Zext(BitSize, Use<Node>),

    Load(MemRef),

    // Mem nodes.
    InMem,

    Store(MemRef, Use<Node>),
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Node::InReg(r) => write!(f, "in.{:?}", r),
            Node::Const(c) => c.fmt(f),
            Node::Int(op, size, a, b) => {
                let get_inline_node = |node: Use<Node>| {
                    let not_inline =
                        DBG_LOCALS.is_set() && DBG_LOCALS.with(|locals| locals.contains_key(&node));
                    if !not_inline && DBG_CX.is_set() {
                        Some(DBG_CX.with(|cx| cx[node]))
                    } else {
                        None
                    }
                };
                let as_unop = |node: Node| node.as_unop(|c| get_inline_node(c)?.as_const());

                // `-x` and `!x`.
                if let Some((unary_op, x)) = as_unop(*self) {
                    return write!(f, "{}{:?}", unary_op, x);
                }

                // `a - b`.
                if let IntOp::Add = op {
                    if let Some(b) = get_inline_node(*b) {
                        if let Some(b) = b.as_const() {
                            // HACK(eddyb) assume adds are subs by constant if
                            // the constant is small in absolute magnitude
                            // (where "small" is less than half the bitwidth).
                            let minus_b = b.as_i64().wrapping_neg();
                            if 0 < minus_b && minus_b < (1 << (size.bits() / 2)) {
                                let minus_b = Const::new(*size, minus_b as u64);
                                return write!(
                                    f,
                                    "{:?} -{} {:?}",
                                    a,
                                    size.bits_subscript(),
                                    minus_b
                                );
                            }
                        }

                        if let Some(('-', b)) = as_unop(b) {
                            return write!(f, "{:?} -{} {:?}", a, size.bits_subscript(), b);
                        }
                    }
                }

                write!(
                    f,
                    "{:?} {}{} {:?}",
                    a,
                    op.as_str(),
                    size.bits_subscript(),
                    b
                )
            }
            Node::Trunc(size, x) => write!(f, "trunc{}({:?})", size.bits_subscript(), x),
            Node::Sext(size, x) => write!(f, "sext{}({:?})", size.bits_subscript(), x),
            Node::Zext(size, x) => write!(f, "zext{}({:?})", size.bits_subscript(), x),
            Node::Load(r) => write!(f, "{:?}[{:?}]{}", r.mem, r.addr, r.size.bits_subscript()),

            Node::InMem => write!(f, "in.m"),
            Node::Store(r, x) => write!(
                f,
                "{:?}[{:?}]{} <- {:?}",
                r.mem,
                r.addr,
                r.size.bits_subscript(),
                x
            ),
        }
    }
}

impl Node {
    // FIXME(eddyb) should these take `&Cx` instead?
    pub fn int_neg(v: Use<Node>) -> impl AllocIn<Interned = Use<Self>> {
        move |cx: &Cx| {
            let size = cx[v].ty().bit_size().unwrap();
            Node::Int(IntOp::Mul, size, v, cx.a(Const::new(size, size.mask())))
        }
    }

    pub fn int_sub(a: Use<Node>, b: Use<Node>) -> impl AllocIn<Interned = Use<Self>> {
        move |cx: &Cx| {
            let size = cx[a].ty().bit_size().unwrap();
            Node::Int(IntOp::Add, size, a, cx.a(Node::int_neg(b)))
        }
    }

    pub fn bit_not(v: Use<Node>) -> impl AllocIn<Interned = Use<Self>> {
        move |cx: &Cx| {
            let size = cx[v].ty().bit_size().unwrap();
            Node::Int(IntOp::Xor, size, v, cx.a(Const::new(size, size.mask())))
        }
    }

    pub fn bit_rol(v: Use<Node>, n: Use<Node>) -> impl AllocIn<Interned = Use<Self>> {
        move |cx: &Cx| {
            let size = cx[v].ty().bit_size().unwrap();
            Node::Int(
                IntOp::Or,
                size,
                cx.a(Node::Int(IntOp::Shl, size, v, n)),
                cx.a(Node::Int(
                    IntOp::ShrU,
                    size,
                    v,
                    cx.a(Node::int_sub(
                        cx.a(Const::new(
                            cx[n].ty().bit_size().unwrap(),
                            size.bits() as u64,
                        )),
                        n,
                    )),
                )),
            )
        }
    }

    pub fn bit_ror(v: Use<Node>, n: Use<Node>) -> impl AllocIn<Interned = Use<Self>> {
        move |cx: &Cx| {
            let size = cx[v].ty().bit_size().unwrap();
            Node::Int(
                IntOp::Or,
                size,
                cx.a(Node::Int(IntOp::ShrU, size, v, n)),
                cx.a(Node::Int(
                    IntOp::Shl,
                    size,
                    v,
                    cx.a(Node::int_sub(
                        cx.a(Const::new(
                            cx[n].ty().bit_size().unwrap(),
                            size.bits() as u64,
                        )),
                        n,
                    )),
                )),
            )
        }
    }

    pub fn ty(&self) -> Type {
        match self {
            Node::InReg(r) => Type::Bits(r.size),
            Node::Const(c) => Type::Bits(c.size),

            Node::Int(IntOp::Eq, _, _, _)
            | Node::Int(IntOp::LtS, _, _, _)
            | Node::Int(IntOp::LtU, _, _, _) => Type::Bits(BitSize::B1),

            Node::Int(_, size, _, _)
            | Node::Trunc(size, _)
            | Node::Sext(size, _)
            | Node::Zext(size, _) => Type::Bits(*size),

            Node::Load(r) => Type::Bits(r.size.into()),

            Node::InMem | Node::Store(..) => Type::Mem,
        }
    }

    pub fn as_const(&self) -> Option<Const> {
        match *self {
            Node::Const(x) => Some(x),
            _ => None,
        }
    }

    /// Returns `Some(('-', x))` for `x * -1`, and `Some(('!', x))` for `x ^ !0`.
    /// Note that `-1` and `!0` are the same all-ones bitpattern.
    fn as_unop(
        &self,
        get_const: impl FnOnce(Use<Node>) -> Option<Const>,
    ) -> Option<(char, Use<Node>)> {
        if let Node::Int(op, size, a, b) = *self {
            if let IntOp::Mul | IntOp::Xor = op {
                let all_ones = Const::new(size, size.mask());
                if get_const(b) == Some(all_ones) {
                    let unary_op = match op {
                        IntOp::Mul => '-',
                        IntOp::Xor => '!',
                        _ => unreachable!(),
                    };
                    return Some((unary_op, a));
                }
            }
        }
        None
    }

    fn normalize(self, cx: &Cx) -> Result<Self, Use<Self>> {
        // TODO(eddyb) resolve loads.

        if let Node::Const(c) = self {
            assert_eq!(c.bits, c.bits & c.size.mask());
        }

        if let Node::Int(op, size, a, b) = self {
            let a_size = cx[a].ty().bit_size().unwrap();
            let b_size = cx[b].ty().bit_size().unwrap();
            assert_eq!(a_size, size);

            let is_shift = match op {
                IntOp::Shl | IntOp::ShrU | IntOp::ShrS => true,
                _ => false,
            };
            if !is_shift {
                assert_eq!(a_size, b_size);
            }

            let c_a = cx[a].as_const();
            let c_b = cx[b].as_const();
            if let Some(r) = op.simplify(c_a.ok_or(a), c_b.ok_or(b)) {
                return r.map(Node::Const);
            }

            // FIXME(eddyb) clean up the naming schemes in these pattern-matches.
            // Maybe introduce some macro to help with performing nested matches?

            // HACK(eddyb) replace `x + a` with `a + x` where `x` is constant.
            // See also the TODO below about sorting symmetric ops.
            if op == IntOp::Add && c_a.is_some() && c_b.is_none() {
                return Node::Int(IntOp::Add, size, b, a).normalize(cx);
            }

            // HACK(eddyb) fuse `(a + x) + y` where `x` and `y` are constants.
            match (op, cx[a], cx[b]) {
                (IntOp::Add, Node::Int(IntOp::Add, _, a, b), Node::Const(y)) => {
                    if let Node::Const(x) = cx[b] {
                        if let Some(xy) = IntOp::Add.eval(x, y) {
                            return Node::Int(IntOp::Add, size, a, cx.a(xy)).normalize(cx);
                        }
                    }
                }
                _ => {}
            }

            // HACK(eddyb) fuse `(a & x) & y` where `x` and `y` are constants.
            match (op, cx[a], cx[b]) {
                (IntOp::And, Node::Int(IntOp::And, _, a, b), Node::Const(y)) => {
                    if let Node::Const(x) = cx[b] {
                        if let Some(xy) = IntOp::And.eval(x, y) {
                            return Node::Int(IntOp::And, size, a, cx.a(xy)).normalize(cx);
                        }
                    }
                }
                _ => {}
            }

            // Simplify `x + x` to `x << 1`.
            if op == IntOp::Add && a == b {
                return Node::Int(IntOp::Shl, size, a, cx.a(Const::new(BitSize::B8, 1)))
                    .normalize(cx);
            }

            // Simplify `x ^ x` to `0`.
            if op == IntOp::Xor && a == b {
                return Ok(Node::Const(Const::new(size, 0)));
            }

            // HACK(eddyb) remove redundant `x & mask` where `x` has enough
            // bits known (e.g. it's an unsigned shift left/right, or zext).
            match (op, cx[a], cx[b]) {
                (IntOp::And, Node::Int(IntOp::Shl, ..), Node::Const(mask))
                | (IntOp::And, Node::Int(IntOp::ShrU, ..), Node::Const(mask))
                | (IntOp::And, Node::Zext(..), Node::Const(mask)) => {
                    let zero = Const::new(size, 0);

                    let present_bits = match cx[a] {
                        Node::Int(shift_op @ IntOp::Shl, _, _, shift)
                        | Node::Int(shift_op @ IntOp::ShrU, _, _, shift) => {
                            let all_ones = Const::new(size, size.mask());
                            cx[shift]
                                .as_const()
                                .and_then(|shift| shift_op.eval(all_ones, shift))
                                .unwrap_or(all_ones)
                        }

                        Node::Zext(_, inner) => {
                            Const::new(size, cx[inner].ty().bit_size().unwrap().mask())
                        }

                        _ => unreachable!(),
                    };

                    if let Some(masked_bits) = IntOp::And.eval(present_bits, mask) {
                        if masked_bits == zero {
                            return Ok(Node::Const(zero));
                        }
                        if masked_bits == present_bits {
                            return Err(a);
                        }
                    }
                }
                _ => {}
            }

            // HACK(eddyb) replace `x >> n << n` or `x << n >> n` with `x & mask`.
            match (op, cx[a], cx[b]) {
                (IntOp::Shl, Node::Int(inner_op @ IntOp::ShrU, _, x, n2), Node::Const(n))
                | (IntOp::ShrU, Node::Int(inner_op @ IntOp::Shl, _, x, n2), Node::Const(n)) => {
                    if cx[n2] == Node::Const(n) {
                        let all_ones = Const::new(size, size.mask());
                        if let Some(inner) = inner_op.eval(all_ones, n) {
                            if let Some(mask) = op.eval(inner, n) {
                                return Node::Int(IntOp::And, size, x, cx.a(mask)).normalize(cx);
                            }
                        }
                    }
                }
                _ => {}
            }

            // HACK(eddyb) replace `(x & c1) | (x & c2)` with `x & (c1 | c2)`.
            match (op, cx[a], cx[b]) {
                (IntOp::Or, Node::Int(IntOp::And, _, x1, c1), Node::Int(IntOp::And, _, x2, c2)) => {
                    if x1 == x2 {
                        if let (Node::Const(c1), Node::Const(c2)) = (cx[c1], cx[c2]) {
                            if let Some(c) = IntOp::Or.eval(c1, c2) {
                                return Node::Int(IntOp::And, size, x1, cx.a(c)).normalize(cx);
                            }
                        }
                    }
                }
                _ => {}
            }

            // HACK(eddyb) replace `(x | y) & c` with `(x & c) | (y & c)`.
            match (op, cx[a], cx[b]) {
                (IntOp::And, Node::Int(IntOp::Or, _, x, y), Node::Const(_)) => {
                    return Node::Int(
                        IntOp::Or,
                        size,
                        cx.a(Node::Int(IntOp::And, size, x, b)),
                        cx.a(Node::Int(IntOp::And, size, y, b)),
                    )
                    .normalize(cx);
                }
                _ => {}
            }
        }

        // FIXME(eddyb) deduplicate these
        if let Node::Trunc(size, x) = self {
            let x_size = cx[x].ty().bit_size().unwrap();
            assert!(size < x_size);

            if let Some(c) = cx[x].as_const() {
                return Ok(Node::Const(Const::new(size, c.as_u64() & size.mask())));
            }

            // HACK(eddyb) replace `trunc({s,z}ext(y))` with something simpler.
            // NOTE(eddyb) this doesn't seem to be hit in practice, maybe remove?
            if let Node::Sext(_, y) | Node::Zext(_, y) = cx[x] {
                let y_size = cx[y].ty().bit_size().unwrap();
                return if size == y_size {
                    Err(y)
                } else if size < y_size {
                    Node::Trunc(size, y).normalize(cx)
                } else {
                    match cx[x] {
                        Node::Sext(..) => Node::Sext(size, y).normalize(cx),
                        Node::Zext(..) => Node::Zext(size, y).normalize(cx),
                        _ => unreachable!(),
                    }
                };
            }
        }

        if let Node::Sext(size, x) = self {
            let x_size = cx[x].ty().bit_size().unwrap();
            assert!(size > x_size);

            if let Some(c) = cx[x].as_const() {
                return Ok(Node::Const(Const::new(
                    size,
                    (c.as_i64() as u64) & size.mask(),
                )));
            }
        }

        if let Node::Zext(size, x) = self {
            let x_size = cx[x].ty().bit_size().unwrap();
            assert!(size > x_size);

            if let Some(c) = cx[x].as_const() {
                return Ok(Node::Const(Const::new(size, c.as_u64())));
            }

            // HACK(eddyb) replace `zext(trunc(y))` by `y & mask`.
            if let Node::Trunc(_, y) = cx[x] {
                let y_size = cx[y].ty().bit_size().unwrap();
                if size == y_size {
                    return Node::Int(
                        IntOp::And,
                        y_size,
                        y,
                        cx.a(Const::new(y_size, x_size.mask())),
                    )
                    .normalize(cx);
                }
            }
        }

        if let Node::Load(r) = self {
            assert_eq!(cx[r.mem].ty(), Type::Mem);
        }

        if let Node::Store(r, v) = self {
            assert_eq!(cx[r.mem].ty(), Type::Mem);

            let r_size: BitSize = r.size.into();
            assert_eq!(cx[v].ty(), Type::Bits(r_size));
        }

        // TODO(eddyb) sort symmetric ops.
        // (eqsat would be better in general, but it's way more work)

        Ok(self)
    }
}

pub trait Visitor: Sized {
    fn cx(&self) -> &Cx;

    fn visit_node(&mut self, node: Use<Node>) {
        node.walk(self);
    }
}

pub trait Visit {
    fn walk(&self, visitor: &mut impl Visitor);
    fn visit(&self, visitor: &mut impl Visitor) {
        self.walk(visitor);
    }
}

impl<A: Visit, B: Visit> Visit for (A, B) {
    fn walk(&self, visitor: &mut impl Visitor) {
        self.0.visit(visitor);
        self.1.visit(visitor);
    }
}

impl<T: Visit> Visit for &'_ T {
    fn walk(&self, visitor: &mut impl Visitor) {
        (**self).walk(visitor);
    }
    fn visit(&self, visitor: &mut impl Visitor) {
        (**self).visit(visitor);
    }
}

impl Visit for Use<Node> {
    fn walk(&self, visitor: &mut impl Visitor) {
        let node = visitor.cx()[*self];
        node.visit(visitor);
    }
    fn visit(&self, visitor: &mut impl Visitor) {
        visitor.visit_node(*self);
    }
}

impl Visit for Node {
    fn walk(&self, visitor: &mut impl Visitor) {
        match *self {
            Node::InReg(_) | Node::Const(_) => {}
            Node::Int(_, _, a, b) => {
                visitor.visit_node(a);
                visitor.visit_node(b);
            }
            Node::Trunc(_, x) | Node::Sext(_, x) | Node::Zext(_, x) => visitor.visit_node(x),
            Node::Load(r) => {
                visitor.visit_node(r.mem);
                visitor.visit_node(r.addr);
            }
            Node::InMem => {}
            Node::Store(r, x) => {
                visitor.visit_node(r.mem);
                visitor.visit_node(r.addr);
                visitor.visit_node(x);
            }
        }
    }
}

impl Use<Node> {
    pub fn subst(self, cx: &Cx, base: &State) -> Self {
        cx.a(match cx[self] {
            Node::InReg(r) => return base.regs[r.index],

            Node::Const(_) => return self,

            Node::Int(op, size, a, b) => Node::Int(op, size, a.subst(cx, base), b.subst(cx, base)),
            Node::Trunc(size, x) => Node::Trunc(size, x.subst(cx, base)),
            Node::Sext(size, x) => Node::Sext(size, x.subst(cx, base)),
            Node::Zext(size, x) => Node::Zext(size, x.subst(cx, base)),

            Node::Load(r) => Node::Load(r.subst(cx, base)),

            Node::InMem => return base.mem,

            Node::Store(r, x) => Node::Store(r.subst(cx, base), x.subst(cx, base)),
        })
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Effect {
    Jump(Use<Node>),

    // FIXME(eddyb) support this better, add Node args, etc.
    Opaque { call: String, next_pc: Use<Node> },

    Error(String),
}

impl fmt::Debug for Effect {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Effect::Jump(target) => write!(f, "jump({:?})", target),
            Effect::Opaque { call, next_pc } => write!(f, "{} -> {:?}", call, next_pc),
            Effect::Error(msg) => write!(f, "error({:?})", msg),
        }
    }
}

impl Visit for Effect {
    fn walk(&self, visitor: &mut impl Visitor) {
        match *self {
            Effect::Jump(target)
            | Effect::Opaque {
                next_pc: target, ..
            } => {
                visitor.visit_node(target);
            }
            Effect::Error(_) => {}
        }
    }
}

#[derive(Clone)]
pub struct State {
    pub mem: Use<Node>,
    pub regs: Vec<Use<Node>>,
}

impl Visit for State {
    fn walk(&self, visitor: &mut impl Visitor) {
        if self.mem != visitor.cx().default.mem {
            visitor.visit_node(self.mem);
        }
        for (i, &v) in self.regs.iter().enumerate() {
            if v != visitor.cx().default.regs[i] {
                visitor.visit_node(v);
            }
        }
    }
}

pub struct Edge {
    pub state: State,
    pub effect: Effect,
}

impl Visit for Edge {
    fn walk(&self, visitor: &mut impl Visitor) {
        self.state.visit(visitor);
        self.effect.visit(visitor);
    }
}

// TODO(eddyb) find better names.
#[derive(Copy, Clone)]
pub enum Edges<T> {
    One(T),
    Branch { cond: Use<Node>, t: T, e: T },
}

impl<T: fmt::Debug> fmt::Debug for Edges<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Edges::One(edge) => write!(f, "{:?}", edge),
            Edges::Branch { cond, t, e } => {
                write!(f, "if {:?} {{ {:?} }} else {{ {:?} }}", cond, t, e)
            }
        }
    }
}

impl<T: Visit> Visit for Edges<T> {
    fn walk(&self, visitor: &mut impl Visitor) {
        match self {
            Edges::One(edge) => {
                edge.visit(visitor);
            }
            Edges::Branch { cond, t, e } => {
                visitor.visit_node(*cond);
                t.visit(visitor);
                e.visit(visitor);
            }
        }
    }
}

impl<T> Edges<T> {
    pub fn as_ref(&self) -> Edges<&T> {
        match self {
            Edges::One(x) => Edges::One(x),
            Edges::Branch { cond, t, e } => Edges::Branch { cond: *cond, t, e },
        }
    }
    pub fn map<U>(self, mut f: impl FnMut(T, Option<bool>) -> U) -> Edges<U> {
        match self {
            Edges::One(x) => Edges::One(f(x, None)),
            Edges::Branch { cond, t, e } => Edges::Branch {
                cond,
                t: f(t, Some(true)),
                e: f(e, Some(false)),
            },
        }
    }
    pub fn merge(self, f: impl FnOnce(T, T) -> T) -> T {
        match self {
            Edges::One(x) => x,
            Edges::Branch { t, e, .. } => f(t, e),
        }
    }
    pub fn get(self, br_cond: Option<bool>) -> T {
        match (self, br_cond) {
            (Edges::One(x), None) => x,
            (Edges::Branch { t, .. }, Some(true)) => t,
            (Edges::Branch { e, .. }, Some(false)) => e,
            _ => unreachable!(),
        }
    }
}

pub struct Block {
    pub pc: RangeTo<Const>,
    pub edges: Edges<Edge>,
}

pub trait Isa {
    fn addr_size(&self) -> BitSize;

    fn default_regs(&self, cx: &Cx) -> Vec<Use<Node>>;

    // FIXME(eddyb) replace the `Result` with a dedicated enum.
    fn lift_instr(&self, cx: &Cx, pc: &mut Const, state: State) -> Result<State, Edges<Edge>>;
}

#[derive(Debug)]
pub struct UnsupportedAddress(pub Const);

pub trait Rom {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress>;
}

pub struct RawRom<T> {
    pub big_endian: bool,
    pub data: T,
}

impl<T: Deref<Target = [u8]>> Rom for RawRom<T> {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        let err = UnsupportedAddress(addr);
        let addr = addr.as_u64();
        if addr >= self.data.len() as u64
            || addr + (size.bits() / 8 - 1) as u64 >= self.data.len() as u64
        {
            return Err(err);
        }
        let b = |i| self.data[addr as usize + i];

        // FIXME(eddyb) deduplicate these if possible.
        Ok(match size {
            MemSize::M8 => Const::new(BitSize::B8, b(0) as u64),
            MemSize::M16 => {
                assert_eq!(addr & 1, 0);

                let bytes = [b(0), b(1)];
                Const::new(
                    BitSize::B16,
                    if self.big_endian {
                        u16::from_be_bytes(bytes)
                    } else {
                        u16::from_le_bytes(bytes)
                    } as u64,
                )
            }
            MemSize::M32 => {
                assert_eq!(addr & 3, 0);

                let bytes = [b(0), b(1), b(2), b(3)];
                Const::new(
                    BitSize::B32,
                    if self.big_endian {
                        u32::from_be_bytes(bytes)
                    } else {
                        u32::from_le_bytes(bytes)
                    } as u64,
                )
            }
            MemSize::M64 => {
                assert_eq!(addr & 7, 0);

                let bytes = [b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7)];
                Const::new(
                    BitSize::B64,
                    if self.big_endian {
                        u64::from_be_bytes(bytes)
                    } else {
                        u64::from_le_bytes(bytes)
                    },
                )
            }
        })
    }
}

// FIXME(eddyb) maybe this and friends (e.g. `Rom`) shouldn't be here.
// but `Cx` uses `Platform`, so some reorganization is needed.
pub trait Platform {
    fn isa(&self) -> &dyn Isa;
    fn rom(&self) -> &dyn Rom;
}

pub struct SimplePlatform<A, R> {
    pub isa: A,
    pub rom: R,
}

impl<A: Isa, R: Rom> Platform for SimplePlatform<A, R> {
    fn isa(&self) -> &dyn Isa {
        &self.isa
    }
    fn rom(&self) -> &dyn Rom {
        &self.rom
    }
}

pub struct Cx {
    stores: Stores,

    pub platform: Box<dyn Platform>,
    pub default: State,
}

impl Cx {
    pub fn pretty_print<'a>(
        &'a self,
        value: &'a (impl Visit + fmt::Debug),
    ) -> impl fmt::Display + 'a {
        self.pretty_print_on_edges(Edges::One(value))
    }
    pub fn pretty_print_on_edges<'a>(
        &'a self,
        edge_values: Edges<&'a (impl Visit + fmt::Debug)>,
    ) -> impl fmt::Display + 'a {
        self.pretty_print_with_states_on_edges(edge_values.map(|value, _| (&self.default, value)))
    }
    pub fn pretty_print_with_states_on_edges<'a>(
        &'a self,
        edge_states_and_values: Edges<(&'a State, &'a (impl Visit + fmt::Debug))>,
    ) -> impl fmt::Display + 'a {
        struct Data {
            use_counts: HashMap<Use<Node>, usize>,
            numbered_counts: HashMap<&'static str, usize>,
            locals: HashMap<Use<Node>, (&'static str, usize)>,
            val_to_state_regs: HashMap<Use<Node>, Vec<Reg>>,
            state_mem: Option<Use<Node>>,
        }

        struct UseCounter<'a> {
            cx: &'a Cx,
            data: &'a mut Data,
        }

        impl Visitor for UseCounter<'_> {
            fn cx(&self) -> &Cx {
                self.cx
            }

            fn visit_node(&mut self, node: Use<Node>) {
                let count = self.data.use_counts.entry(node).or_insert(0);
                *count += 1;
                if *count == 1 {
                    node.walk(self);
                }
            }
        }

        struct Numberer<'a> {
            cx: &'a Cx,
            data: &'a mut Data,
            allow_inline: bool,
        }

        impl Visitor for Numberer<'_> {
            fn cx(&self) -> &Cx {
                self.cx
            }

            fn visit_node(&mut self, node: Use<Node>) {
                if self.data.locals.contains_key(&node) {
                    return;
                }

                let allowed_inline = mem::replace(&mut self.allow_inline, false);
                match self.cx[node] {
                    Node::Trunc(_, x) | Node::Sext(_, x) | Node::Zext(_, x) => {
                        self.allow_inline = true;
                        self.visit_node(x);
                    }
                    Node::Load(r) => {
                        self.visit_node(r.mem);

                        self.allow_inline = true;
                        self.visit_node(r.addr);
                    }
                    Node::Store(r, x) => {
                        self.visit_node(r.mem);

                        self.allow_inline = true;
                        self.visit_node(r.addr);
                        self.visit_node(x);
                    }
                    _ => node.walk(self),
                }
                self.allow_inline = allowed_inline;

                // HACK(eddyb) override `allowed_inline` for nodes we want to
                // inline, but *only* if they're used exactly once.
                let allowed_inline = match self.cx[node] {
                    Node::Trunc(..) | Node::Sext(..) | Node::Zext(..) | Node::Load(_) => true,
                    _ => allowed_inline,
                };

                let inline = match self.cx[node] {
                    Node::InReg(_) | Node::Const(_) | Node::InMem => true,

                    // `-x` and `!x`.
                    _ if self.cx[node].as_unop(|c| self.cx[c].as_const()).is_some() => true,

                    _ => allowed_inline && self.data.use_counts[&node] == 1,
                };
                if !inline {
                    let prefix = match self.cx[node].ty() {
                        Type::Bits(_) => "v",
                        Type::Mem => "m",
                    };
                    let numbered_count = self.data.numbered_counts.entry(prefix).or_default();
                    let next = *numbered_count;
                    *numbered_count += 1;
                    self.data.locals.insert(node, (prefix, next));
                }
            }
        }

        struct Printer<'a, F> {
            cx: &'a Cx,
            data: &'a Data,
            fmt: &'a mut F,
            seen: HashSet<Use<Node>>,
            empty: bool,
        }

        impl<F: fmt::Write> Printer<'_, F> {
            fn start_def(&mut self) {
                if self.empty {
                    self.empty = false;
                    let _ = writeln!(self.fmt, "{{");
                }
                let _ = write!(self.fmt, "    ");
            }
        }

        impl<F: fmt::Write> Visitor for Printer<'_, F> {
            fn cx(&self) -> &Cx {
                self.cx
            }

            fn visit_node(&mut self, node: Use<Node>) {
                if !self.seen.insert(node) {
                    return;
                }
                node.walk(self);

                let mut names = 0;
                macro_rules! write_name {
                    ($fmt_str:literal $($rest:tt)*) => {{
                        if names == 0 {
                            self.start_def();
                        }
                        let _ = write!(self.fmt, concat!($fmt_str, " = ") $($rest)*);
                        names += 1;
                    }}
                }

                if let Some(regs) = self.data.val_to_state_regs.get(&node) {
                    for r in regs {
                        write_name!("{:?}", r);
                    }
                }
                if Some(node) == self.data.state_mem {
                    write_name!("m");
                }

                if self.data.locals.contains_key(&node) {
                    if names < self.data.use_counts[&node] {
                        write_name!("{:?}", node);
                    }
                }
                if names > 0 {
                    let _ = writeln!(self.fmt, "{:?};", self.cx[node]);
                }
            }
        }

        let mut data = Data {
            use_counts: Default::default(),
            numbered_counts: Default::default(),
            locals: Default::default(),
            val_to_state_regs: Default::default(),
            state_mem: None,
        };

        let mut use_counter = UseCounter {
            cx: self,
            data: &mut data,
        };

        {
            let default = self.default.mem;
            let m = edge_states_and_values
                .map(|(state, _), _| state.mem)
                .merge(|t, e| {
                    if t == e {
                        t
                    } else {
                        use_counter.visit_node(t);
                        use_counter.visit_node(e);
                        default
                    }
                });
            if m != default {
                use_counter.data.state_mem = Some(m);
                use_counter.visit_node(m);
            }
        }

        for (i, &default) in self.default.regs.iter().enumerate() {
            let v = edge_states_and_values
                .map(|(state, _), _| state.regs[i])
                .merge(|t, e| {
                    if t == e {
                        t
                    } else {
                        use_counter.visit_node(t);
                        use_counter.visit_node(e);
                        default
                    }
                });
            if v == default {
                continue;
            }

            // HACK(eddyb) try to guess the register name.
            // Ideally this would be provided by the `Isa`.
            let r = match self[default] {
                Node::InReg(r) if i == r.index => r,
                default => panic!("register #{} has non-register default {:?}", i, default),
            };
            use_counter
                .data
                .val_to_state_regs
                .entry(v)
                .or_default()
                .push(r);
            use_counter.visit_node(v);
        }
        edge_states_and_values
            .map(|(_, value), _| value)
            .visit(&mut use_counter);

        edge_states_and_values.visit(&mut Numberer {
            cx: self,
            data: &mut data,
            allow_inline: true,
        });

        struct PrintFromDisplay<'a, T> {
            cx: &'a Cx,
            data: Data,

            edge_states_and_values: Edges<(&'a State, &'a T)>,
        }

        impl<T> fmt::Display for PrintFromDisplay<'_, T>
        where
            T: Visit + fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let dbg_tls_inner_print = || {
                    // FIXME(eddyb) proper error-handling.
                    let mut printer = Printer {
                        cx: self.cx,
                        data: &self.data,
                        fmt: f,
                        seen: Default::default(),
                        empty: true,
                    };
                    self.edge_states_and_values.visit(&mut printer);
                    let block_opened = !printer.empty;

                    match self.edge_states_and_values {
                        Edges::One((_, value)) => {
                            if block_opened {
                                write!(f, "    ")?;
                            }
                            write!(f, "{:?}", value)?;
                            if block_opened {
                                write!(f, "\n}}")?;
                            }
                        }
                        Edges::Branch { cond, t, e } => {
                            // HACK(eddyb) always print if-else multi-line.
                            if !block_opened {
                                writeln!(f, "{{")?;
                            }

                            let print_edge =
                                |f: &mut fmt::Formatter,
                                 (state, value): (&State, _),
                                 (other_state, _): (&State, _)| {
                                    {
                                        let default = self.cx.default.mem;
                                        let m = state.mem;
                                        if m != default && m != other_state.mem {
                                            writeln!(f, "        m = {:?};", m)?;
                                        }
                                    }
                                    for (i, &default) in self.cx.default.regs.iter().enumerate() {
                                        let v = state.regs[i];
                                        if v != default && v != other_state.regs[i] {
                                            // HACK(eddyb) try to guess the register name.
                                            // Ideally this would be provided by the `Isa`.
                                            let r = match self.cx[default] {
                                                Node::InReg(r) if i == r.index => r,
                                                default => panic!(
                                                    "register #{} has non-register default {:?}",
                                                    i, default
                                                ),
                                            };
                                            writeln!(f, "        {:?} = {:?};", r, v)?;
                                        }
                                    }
                                    writeln!(f, "        {:?}", value)
                                };

                            writeln!(f, "    if {:?} {{", cond)?;
                            print_edge(f, t, e)?;
                            writeln!(f, "    }} else {{")?;
                            print_edge(f, e, t)?;
                            writeln!(f, "    }}")?;
                            write!(f, "}}")?;
                        }
                    }

                    Ok(())
                };
                DBG_CX.set(self.cx, || {
                    DBG_LOCALS.set(&self.data.locals, dbg_tls_inner_print)
                })
            }
        }

        PrintFromDisplay {
            cx: self,
            data,

            edge_states_and_values,
        }
    }
}

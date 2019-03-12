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

    use std::cmp::Ordering;
    use std::collections::hash_map::Entry;
    use std::collections::HashMap;
    use std::hash::{Hash, Hasher};

    pub struct Use<T> {
        key: slotmap::KeyData,
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
            self.key == other.key
        }
    }
    impl<T> Eq for Use<T> {}

    impl<T> PartialOrd for Use<T> {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.key.partial_cmp(&other.key)
        }
    }
    impl<T> Ord for Use<T> {
        fn cmp(&self, other: &Self) -> Ordering {
            self.key.cmp(&other.key)
        }
    }

    impl<T> Hash for Use<T> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.key.hash(state);
        }
    }

    impl<T> From<slotmap::KeyData> for Use<T> {
        fn from(key: slotmap::KeyData) -> Self {
            Use {
                key,
                _marker: PhantomData,
            }
        }
    }

    impl<T> From<Use<T>> for slotmap::KeyData {
        fn from(u: Use<T>) -> Self {
            u.key
        }
    }

    impl<T> slotmap::Key for Use<T> {}

    #[derive(Default)]
    pub struct PerKind<Val, Mem> {
        pub val: Val,
        pub mem: Mem,
    }

    pub struct Store<T: slotmap::Slottable> {
        slots: slotmap::SlotMap<Use<T>, T>,
        map: HashMap<T, Use<T>>,
    }

    pub(super) type Stores = PerKind<Store<Val>, Store<Mem>>;

    impl<T: slotmap::Slottable + Eq + Hash> Default for Store<T> {
        fn default() -> Self {
            Store {
                slots: Default::default(),
                map: Default::default(),
            }
        }
    }

    impl<T: slotmap::Slottable> Index<Use<T>> for Store<T> {
        type Output = T;
        fn index(&self, u: Use<T>) -> &T {
            &self.slots[u]
        }
    }

    impl<T: Copy + Eq + Hash> Store<T> {
        fn alloc(&mut self, x: T) -> Use<T> {
            match self.map.entry(x) {
                Entry::Occupied(entry) => *entry.get(),
                Entry::Vacant(entry) => *entry.insert(self.slots.insert(x)),
            }
        }
    }

    impl<P: Platform> Cx<P> {
        pub fn new(platform: P) -> Self {
            let mut stores = Stores::default();

            let default = State {
                mem: stores.mem.alloc(Mem::In),
                regs: vec![],
            };

            let mut cx = Cx {
                stores,
                platform,
                default,
            };

            cx.default.regs = P::Arch::default_regs(&mut cx);

            cx
        }
    }

    pub trait AllocIn<C>: Sized {
        type Kind;
        fn alloc_in(self, cx: &mut C) -> Use<Self::Kind>;
    }

    impl<C, K: AllocIn<C, Kind = K>, F: FnOnce(&mut C) -> K> AllocIn<C> for F {
        type Kind = K;
        fn alloc_in(self, cx: &mut C) -> Use<K> {
            self(cx).alloc_in(cx)
        }
    }

    impl<P> Cx<P> {
        pub fn a<T: AllocIn<Self>>(&mut self, x: T) -> Use<T::Kind> {
            x.alloc_in(self)
        }
    }

    macro_rules! per_kind_impls {
        ($field:ident: $k:ident, fmt($prefix:literal)) => {
            impl<Val, Mem> Index<Use<super::$k>> for PerKind<Val, Mem>
            where
                $k: Index<Use<super::$k>>,
            {
                type Output = $k::Output;
                fn index(&self, u: Use<super::$k>) -> &Self::Output {
                    self.$field.index(u)
                }
            }

            impl<P> AllocIn<Cx<P>> for $k {
                type Kind = Self;
                fn alloc_in(self, cx: &mut Cx<P>) -> Use<Self> {
                    match self.normalize(cx) {
                        Ok(x) => cx.stores.$field.alloc(x),
                        Err(u) => u,
                    }
                }
            }

            impl fmt::Debug for Use<$k> {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    let local = if DBG_LOCALS.is_set() {
                        DBG_LOCALS.with(|maps| maps.$field.get(self).cloned())
                    } else {
                        None
                    };
                    match local {
                        Some(Ok(i)) => write!(f, concat!($prefix, "{}"), i),
                        Some(Err(x)) => write!(f, "{:?}", x),
                        None => {
                            let k = self.key.as_ffi();
                            let (hi, lo) = ((k >> 32) as u32, k as u32);
                            write!(f, concat!($prefix, "#{:x}:{:x}"), hi, lo)
                        }
                    }
                }
            }
        };
    }

    per_kind_impls!(val: Val, fmt("v"));
    per_kind_impls!(mem: Mem, fmt("m"));
}

scoped_thread_local!(static DBG_LOCALS: PerKind<
    HashMap<Use<Val>, Result<usize, Val>>,
    HashMap<Use<Mem>, Result<usize, Mem>>,
>);

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

impl<P> AllocIn<Cx<P>> for Const {
    type Kind = Val;
    fn alloc_in(self, cx: &mut Cx<P>) -> Use<Val> {
        cx.a(Val::Const(self))
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
    MulS,
    MulU,
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
            IntOp::MulS | IntOp::DivS | IntOp::RemS | IntOp::LtS | IntOp::ShrS => true,
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
        let b = if is_signed && !is_shift {
            b.as_i64() as u64
        } else {
            b.as_u64()
        };

        let r = match self {
            IntOp::Add => a.wrapping_add(b),
            IntOp::MulS => (a as i64 as i128 * b as i64 as i128) as u64,
            IntOp::MulU => (a as u128 * b as u128) as u64,
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

            IntOp::Shl => a.wrapping_shl(b as u32),
            IntOp::ShrS => (a as i64).wrapping_shr(b as u32) as u64,
            IntOp::ShrU => a.wrapping_shr(b as u32),
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
                | (IntOp::MulS, 1)
                | (IntOp::MulU, 1)
                | (IntOp::And, -1)
                | (IntOp::Or, 0)
                | (IntOp::Xor, 0) => return Some(Err(other)),

                (IntOp::MulS, 0) | (IntOp::MulU, 0) | (IntOp::And, 0) | (IntOp::Or, -1) => {
                    return Some(Ok(x))
                }

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
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct MemRef {
    pub mem: Use<Mem>,
    pub addr: Use<Val>,
    pub size: MemSize,
}

impl fmt::Debug for MemRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}.{}[{:?}]", self.mem, self.size.bits(), self.addr)
    }
}

impl MemRef {
    pub fn subst<P>(self, cx: &mut Cx<P>, base: &State) -> Self {
        MemRef {
            mem: self.mem.subst(cx, base),
            addr: self.addr.subst(cx, base),
            size: self.size,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Val {
    InReg(Reg),

    Const(Const),
    Int(IntOp, BitSize, Use<Val>, Use<Val>),
    Trunc(BitSize, Use<Val>),
    Sext(BitSize, Use<Val>),
    Zext(BitSize, Use<Val>),

    Load(MemRef),
}

impl fmt::Debug for Val {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Val::InReg(r) => write!(f, "in.{:?}", r),
            Val::Const(c) => c.fmt(f),
            Val::Int(op, size, a, b) => write!(f, "{:?}.{}({:?}, {:?})", op, size.bits(), a, b),
            Val::Trunc(size, x) => write!(f, "Trunc.{}({:?})", size.bits(), x),
            Val::Sext(size, x) => write!(f, "Sext.{}({:?})", size.bits(), x),
            Val::Zext(size, x) => write!(f, "Zext.{}({:?})", size.bits(), x),
            Val::Load(r) => write!(f, "{:?}.Load.{}({:?})", r.mem, r.size.bits(), r.addr),
        }
    }
}

impl Val {
    pub fn int_neg<P>(v: Use<Val>) -> impl AllocIn<Cx<P>, Kind = Self> {
        move |cx: &mut Cx<P>| {
            let size = cx[v].size();
            Val::Int(IntOp::MulS, size, v, cx.a(Const::new(size, size.mask())))
        }
    }

    pub fn int_sub<P>(a: Use<Val>, b: Use<Val>) -> impl AllocIn<Cx<P>, Kind = Self> {
        move |cx: &mut Cx<P>| {
            let size = cx[a].size();
            Val::Int(IntOp::Add, size, a, cx.a(Val::int_neg(b)))
        }
    }

    pub fn bit_not<P>(v: Use<Val>) -> impl AllocIn<Cx<P>, Kind = Self> {
        move |cx: &mut Cx<P>| {
            let size = cx[v].size();
            Val::Int(IntOp::Xor, size, v, cx.a(Const::new(size, size.mask())))
        }
    }

    pub fn bit_rol<P>(v: Use<Val>, n: Use<Val>) -> impl AllocIn<Cx<P>, Kind = Self> {
        move |cx: &mut Cx<P>| {
            let size = cx[v].size();
            let bits = cx.a(Const::new(cx[n].size(), size.bits() as u64));
            let bits_minus_n = cx.a(Val::int_sub(bits, n));
            Val::Int(
                IntOp::Or,
                size,
                cx.a(Val::Int(IntOp::Shl, size, v, n)),
                cx.a(Val::Int(IntOp::ShrU, size, v, bits_minus_n)),
            )
        }
    }

    pub fn bit_ror<P>(v: Use<Val>, n: Use<Val>) -> impl AllocIn<Cx<P>, Kind = Self> {
        move |cx: &mut Cx<P>| {
            let size = cx[v].size();
            let bits = cx.a(Const::new(cx[n].size(), size.bits() as u64));
            let bits_minus_n = cx.a(Val::int_sub(bits, n));
            Val::Int(
                IntOp::Or,
                size,
                cx.a(Val::Int(IntOp::ShrU, size, v, n)),
                cx.a(Val::Int(IntOp::Shl, size, v, bits_minus_n)),
            )
        }
    }

    pub fn size(&self) -> BitSize {
        match self {
            Val::InReg(r) => r.size,
            Val::Const(c) => c.size,

            Val::Int(IntOp::Eq, _, _, _)
            | Val::Int(IntOp::LtS, _, _, _)
            | Val::Int(IntOp::LtU, _, _, _) => BitSize::B1,

            Val::Int(_, size, _, _)
            | Val::Trunc(size, _)
            | Val::Sext(size, _)
            | Val::Zext(size, _) => *size,
            Val::Load(r) => r.size.into(),
        }
    }

    pub fn as_const(&self) -> Option<Const> {
        match *self {
            Val::Const(x) => Some(x),
            _ => None,
        }
    }

    fn normalize<P>(mut self, cx: &mut Cx<P>) -> Result<Self, Use<Self>> {
        // TODO(eddyb) resolve loads.

        if let Val::Const(c) = self {
            assert_eq!(c.bits, c.bits & c.size.mask());
        }

        if let Val::Int(op, size, a, b) = self {
            let a_size = cx[a].size();
            assert_eq!(a_size, size);

            let is_shift = match op {
                IntOp::Shl | IntOp::ShrU | IntOp::ShrS => true,
                _ => false,
            };
            if !is_shift {
                assert_eq!(a_size, cx[b].size());
            }

            let c_a = cx[a].as_const();
            let c_b = cx[b].as_const();
            if let Some(r) = op.simplify(c_a.ok_or(a), c_b.ok_or(b)) {
                match r {
                    Ok(x) => self = Val::Const(x),
                    Err(x) => return Err(x),
                }
            }

            // HACK(eddyb) fuse `(a + x) + y` where `x` and `y` are constants.
            match (op, cx[a], cx[b]) {
                (IntOp::Add, Val::Int(IntOp::Add, _, a, b), Val::Const(y)) => {
                    if let Val::Const(x) = cx[b] {
                        if let Some(xy) = IntOp::Add.eval(x, y) {
                            return Val::Int(IntOp::Add, size, a, cx.a(xy)).normalize(cx);
                        }
                    }
                }
                _ => {}
            }
        }

        // FIXME(eddyb) deduplicate these
        if let Val::Trunc(size, x) = self {
            let x_size = cx[x].size();
            assert!(size < x_size);

            if let Some(c) = cx[x].as_const() {
                self = Val::Const(Const::new(size, c.as_u64() & size.mask()));
            }
        }

        if let Val::Sext(size, x) = self {
            let x_size = cx[x].size();
            assert!(size > x_size);

            if let Some(c) = cx[x].as_const() {
                self = Val::Const(Const::new(size, (c.as_i64() as u64) & size.mask()));
            }
        }

        if let Val::Zext(size, x) = self {
            let x_size = cx[x].size();
            assert!(size > x_size);

            if let Some(c) = cx[x].as_const() {
                self = Val::Const(Const::new(size, c.as_u64()));
            }
        }

        // TODO(eddyb) sort symmetric ops.
        // (eqsat would be better in general, but it's way more work)

        Ok(self)
    }
}

pub trait Visitor: Sized {
    type Platform;

    fn cx(&self) -> &Cx<Self::Platform>;

    fn visit_val_use(&mut self, v: Use<Val>) {
        v.walk(self);
    }
    fn visit_mem_use(&mut self, m: Use<Mem>) {
        m.walk(self);
    }
    fn visit_val(&mut self, val: &Val) {
        val.walk(self);
    }
    fn visit_mem(&mut self, mem: &Mem) {
        mem.walk(self);
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

impl Visit for Use<Val> {
    fn walk(&self, visitor: &mut impl Visitor) {
        let val = visitor.cx()[*self];
        val.visit(visitor);
    }
    fn visit(&self, visitor: &mut impl Visitor) {
        visitor.visit_val_use(*self);
    }
}

impl Visit for Val {
    fn walk(&self, visitor: &mut impl Visitor) {
        match *self {
            Val::InReg(_) | Val::Const(_) => {}
            Val::Int(_, _, a, b) => {
                visitor.visit_val_use(a);
                visitor.visit_val_use(b);
            }
            Val::Trunc(_, x) | Val::Sext(_, x) | Val::Zext(_, x) => visitor.visit_val_use(x),
            Val::Load(r) => {
                visitor.visit_mem_use(r.mem);
                visitor.visit_val_use(r.addr);
            }
        }
    }
    fn visit(&self, visitor: &mut impl Visitor) {
        visitor.visit_val(self);
    }
}

impl Use<Val> {
    pub fn subst<P>(self, cx: &mut Cx<P>, base: &State) -> Self {
        let v = match cx[self] {
            Val::InReg(r) => return base.regs[r.index],

            Val::Const(_) => return self,

            Val::Int(op, size, a, b) => Val::Int(op, size, a.subst(cx, base), b.subst(cx, base)),
            Val::Trunc(size, x) => Val::Trunc(size, x.subst(cx, base)),
            Val::Sext(size, x) => Val::Sext(size, x.subst(cx, base)),
            Val::Zext(size, x) => Val::Zext(size, x.subst(cx, base)),
            Val::Load(r) => Val::Load(r.subst(cx, base)),
        };
        cx.a(v)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Mem {
    In,

    Store(MemRef, Use<Val>),
}

impl fmt::Debug for Mem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Mem::In => write!(f, "in.m"),
            Mem::Store(r, x) => write!(
                f,
                "{:?}.Store.{}({:?}, {:?})",
                r.mem,
                r.size.bits(),
                r.addr,
                x
            ),
        }
    }
}

impl Mem {
    fn normalize<P>(self, cx: &mut Cx<P>) -> Result<Self, Use<Self>> {
        if let Mem::Store(r, v) = self {
            let r_size: BitSize = r.size.into();
            assert_eq!(r_size, cx[v].size());
        }

        Ok(self)
    }
}

impl Visit for Use<Mem> {
    fn walk(&self, visitor: &mut impl Visitor) {
        let mem = visitor.cx()[*self];
        mem.visit(visitor);
    }
    fn visit(&self, visitor: &mut impl Visitor) {
        visitor.visit_mem_use(*self);
    }
}

impl Visit for Mem {
    fn walk(&self, visitor: &mut impl Visitor) {
        match *self {
            Mem::In => {}
            Mem::Store(r, x) => {
                visitor.visit_mem_use(r.mem);
                visitor.visit_val_use(r.addr);
                visitor.visit_val_use(x);
            }
        }
    }
    fn visit(&self, visitor: &mut impl Visitor) {
        visitor.visit_mem(self);
    }
}

impl Use<Mem> {
    pub fn subst<P>(self, cx: &mut Cx<P>, base: &State) -> Self {
        let m = match cx[self] {
            Mem::In => return base.mem,

            Mem::Store(r, x) => Mem::Store(r.subst(cx, base), x.subst(cx, base)),
        };
        cx.a(m)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum Effect {
    Jump(Use<Val>),
    PlatformCall { code: u32, ret_pc: Use<Val> },
    Trap { code: u32 },
}

impl fmt::Debug for Effect {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Effect::Jump(target) => write!(f, "Jump({:?})", target),
            Effect::PlatformCall { code, ret_pc } => {
                write!(f, "PlatformCall({}) -> {:?}", code, ret_pc)
            }
            Effect::Trap { code } => write!(f, "Trap({})", code),
        }
    }
}

impl Visit for Effect {
    fn walk(&self, visitor: &mut impl Visitor) {
        match *self {
            Effect::Jump(target) => {
                visitor.visit_val_use(target);
            }
            Effect::PlatformCall { .. } | Effect::Trap { .. } => {}
        }
    }
}

#[derive(Clone)]
pub struct State {
    pub mem: Use<Mem>,
    pub regs: Vec<Use<Val>>,
}

impl Visit for State {
    fn walk(&self, visitor: &mut impl Visitor) {
        if self.mem != visitor.cx().default.mem {
            visitor.visit_mem_use(self.mem);
        }
        for (i, &v) in self.regs.iter().enumerate() {
            if v != visitor.cx().default.regs[i] {
                visitor.visit_val_use(v);
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
    Branch { cond: Use<Val>, t: T, e: T },
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
                visitor.visit_val_use(*cond);
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

pub trait Arch: Sized {
    const ADDR_SIZE: BitSize;

    fn default_regs(cx: &mut Cx<impl Platform<Arch = Self>>) -> Vec<Use<Val>>;

    // FIXME(eddyb) replace the `Result` with a dedicated enum.
    fn lift_instr(
        cx: &mut Cx<impl Platform<Arch = Self>>,
        pc: &mut Const,
        state: State,
    ) -> Result<State, Edges<Edge>>;
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
// but `Cx<P>` requires `P: Platform`, so some reorganization is needed.
pub trait Platform {
    type Arch: Arch;
    type Rom: Rom;

    fn arch(&self) -> &Self::Arch;
    fn rom(&self) -> &Self::Rom;
}

pub struct SimplePlatform<A, R> {
    pub arch: A,
    pub rom: R,
}

impl<A: Arch, R: Rom> Platform for SimplePlatform<A, R> {
    type Arch = A;
    type Rom = R;

    fn arch(&self) -> &Self::Arch {
        &self.arch
    }
    fn rom(&self) -> &Self::Rom {
        &self.rom
    }
}

pub struct Cx<P> {
    stores: Stores,

    pub platform: P,
    pub default: State,
}

impl<K, P> Index<K> for Cx<P>
where
    Stores: Index<K>,
{
    type Output = <Stores as Index<K>>::Output;
    fn index(&self, k: K) -> &Self::Output {
        self.stores.index(k)
    }
}

impl<P> Cx<P> {
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
            use_counts: PerKind<HashMap<Use<Val>, usize>, HashMap<Use<Mem>, usize>>,
            numbered_counts: PerKind<usize, usize>,
            locals: PerKind<
                HashMap<Use<Val>, Result<usize, Val>>,
                HashMap<Use<Mem>, Result<usize, Mem>>,
            >,
            val_to_state_regs: HashMap<Use<Val>, Vec<Reg>>,
            state_mem: Option<Use<Mem>>,
        }

        struct UseCounter<'a, P> {
            cx: &'a Cx<P>,
            data: &'a mut Data,
        }

        impl<P> Visitor for UseCounter<'_, P> {
            type Platform = P;

            fn cx(&self) -> &Cx<Self::Platform> {
                self.cx
            }

            fn visit_val_use(&mut self, v: Use<Val>) {
                let count = self.data.use_counts.val.entry(v).or_insert(0);
                *count += 1;
                if *count == 1 {
                    v.walk(self);
                }
            }
            fn visit_mem_use(&mut self, m: Use<Mem>) {
                let count = self.data.use_counts.mem.entry(m).or_insert(0);
                *count += 1;
                if *count == 1 {
                    m.walk(self);
                }
            }
        }

        struct Numberer<'a, P> {
            cx: &'a Cx<P>,
            data: &'a mut Data,
            allow_inline: bool,
        }

        impl<P> Visitor for Numberer<'_, P> {
            type Platform = P;

            fn cx(&self) -> &Cx<Self::Platform> {
                self.cx
            }

            fn visit_val_use(&mut self, v: Use<Val>) {
                if self.data.locals.val.contains_key(&v) {
                    return;
                }

                let allowed_inline = mem::replace(&mut self.allow_inline, false);
                v.walk(self);
                self.allow_inline = allowed_inline;

                let val = self.cx[v];
                let inline = match val {
                    Val::InReg(_) | Val::Const(_) => true,
                    _ => allowed_inline && self.data.use_counts.val[&v] == 1,
                };
                let local = if inline {
                    Err(val)
                } else {
                    let next = self.data.numbered_counts.val;
                    self.data.numbered_counts.val += 1;
                    Ok(next)
                };
                self.data.locals.val.insert(v, local);
            }
            fn visit_mem_use(&mut self, m: Use<Mem>) {
                if self.data.locals.mem.contains_key(&m) {
                    return;
                }

                let allowed_inline = mem::replace(&mut self.allow_inline, false);
                m.walk(self);
                self.allow_inline = allowed_inline;

                let mem = self.cx[m];
                let inline = match mem {
                    Mem::In => true,
                    _ => allowed_inline && self.data.use_counts.mem[&m] == 1,
                };
                let local = if inline {
                    Err(mem)
                } else {
                    let next = self.data.numbered_counts.mem;
                    self.data.numbered_counts.mem += 1;
                    Ok(next)
                };
                self.data.locals.mem.insert(m, local);
            }
        }

        struct Printer<'a, P, F> {
            cx: &'a Cx<P>,
            data: &'a Data,
            fmt: &'a mut F,
            seen: PerKind<HashSet<Use<Val>>, HashSet<Use<Mem>>>,
            empty: bool,
        }

        impl<P, F: fmt::Write> Printer<'_, P, F> {
            fn start_def(&mut self) {
                if self.empty {
                    self.empty = false;
                    let _ = writeln!(self.fmt, "{{");
                }
                let _ = write!(self.fmt, "    ");
            }
        }

        impl<P, F: fmt::Write> Visitor for Printer<'_, P, F> {
            type Platform = P;

            fn cx(&self) -> &Cx<Self::Platform> {
                self.cx
            }

            fn visit_val_use(&mut self, v: Use<Val>) {
                if !self.seen.val.insert(v) {
                    return;
                }
                v.walk(self);

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

                if let Some(regs) = self.data.val_to_state_regs.get(&v) {
                    for r in regs {
                        write_name!("{:?}", r);
                    }
                }
                if self.data.locals.val[&v].is_ok() {
                    if names < self.data.use_counts.val[&v] {
                        write_name!("{:?}", v);
                    }
                }
                if names > 0 {
                    let _ = writeln!(self.fmt, "{:?};", self.cx[v]);
                }
            }
            fn visit_mem_use(&mut self, m: Use<Mem>) {
                if !self.seen.mem.insert(m) {
                    return;
                }
                m.walk(self);

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

                if Some(m) == self.data.state_mem {
                    write_name!("m");
                }
                if self.data.locals.mem[&m].is_ok() {
                    if names < self.data.use_counts.mem[&m] {
                        write_name!("{:?}", m);
                    }
                }
                if names > 0 {
                    let _ = writeln!(self.fmt, "{:?};", self.cx[m]);
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
                        use_counter.visit_mem_use(t);
                        use_counter.visit_mem_use(e);
                        default
                    }
                });
            if m != default {
                use_counter.data.state_mem = Some(m);
                use_counter.visit_mem_use(m);
            }
        }

        for (i, &default) in self.default.regs.iter().enumerate() {
            let v = edge_states_and_values
                .map(|(state, _), _| state.regs[i])
                .merge(|t, e| {
                    if t == e {
                        t
                    } else {
                        use_counter.visit_val_use(t);
                        use_counter.visit_val_use(e);
                        default
                    }
                });
            if v == default {
                continue;
            }

            // HACK(eddyb) try to guess the register name.
            // Ideally this would be provided by the `Arch`.
            let r = match self[default] {
                Val::InReg(r) if i == r.index => r,
                default => panic!("register #{} has non-register default {:?}", i, default),
            };
            use_counter
                .data
                .val_to_state_regs
                .entry(v)
                .or_default()
                .push(r);
            use_counter.visit_val_use(v);
        }
        edge_states_and_values
            .map(|(_, value), _| value)
            .visit(&mut use_counter);

        edge_states_and_values.visit(&mut Numberer {
            cx: self,
            data: &mut data,
            allow_inline: true,
        });

        struct PrintFromDisplay<'a, P, T> {
            cx: &'a Cx<P>,
            data: Data,

            edge_states_and_values: Edges<(&'a State, &'a T)>,
        }

        impl<P, T> fmt::Display for PrintFromDisplay<'_, P, T>
        where
            T: Visit + fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                DBG_LOCALS.set(&self.data.locals, || {
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
                                            // Ideally this would be provided by the `Arch`.
                                            let r = match self.cx[default] {
                                                Val::InReg(r) if i == r.index => r,
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

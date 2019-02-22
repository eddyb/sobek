use scoped_tls::scoped_thread_local;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::marker::PhantomData;
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
}

impl BitSize {
    fn bits(self) -> u8 {
        match self {
            BitSize::B1 => 1,
            BitSize::B8 => 8,
            BitSize::B16 => 16,
            BitSize::B32 => 32,
        }
    }

    fn mask(self) -> u32 {
        !0 >> (32 - self.bits())
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Const {
    pub size: BitSize,
    bits: u32,
}

impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (hi, lo) = ((self.bits >> 16) as u16, self.bits as u16);
        if hi != 0 {
            write!(f, "0x{:04x}_{:04x}", hi, lo)
        } else if lo > 9 {
            write!(f, "0x{:04x}", lo)
        } else {
            write!(f, "{}", lo)
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
        Const::new(BitSize::B1, b as u32)
    }
}

impl Const {
    pub fn new(size: BitSize, bits: u32) -> Self {
        assert_eq!(bits, bits & size.mask());

        Const { size, bits }
    }

    pub fn sext32(&self) -> i32 {
        let n = 32 - self.size.bits();
        (self.bits as i32) << n >> n
    }

    pub fn zext32(&self) -> u32 {
        let n = 32 - self.size.bits();
        self.bits << n >> n
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntOp {
    Add,
    // HACK(eddyb) `Hi` variants work around 32-bit datapath.
    MulS,
    MulHiS,
    MulU,
    MulHiU,
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
            IntOp::MulS | IntOp::MulHiS | IntOp::DivS | IntOp::RemS | IntOp::LtS | IntOp::ShrS => {
                true
            }
            _ => false,
        };
        if !is_shift {
            assert_eq!(a.size, b.size);
        }
        let a = if is_signed {
            a.sext32() as u32
        } else {
            a.zext32()
        };
        let b = if is_signed && !is_shift {
            b.sext32() as u32
        } else {
            b.zext32()
        };

        let mul_s = |a, b| a as i32 as i64 * b as i32 as i64;
        let mul_u = |a, b| a as u64 * b as u64;
        let r = match self {
            IntOp::Add => a.wrapping_add(b),
            IntOp::MulS => mul_s(a, b) as u32,
            IntOp::MulHiS => (mul_s(a, b) >> 32) as u32,
            IntOp::MulU => mul_u(a, b) as u32,
            IntOp::MulHiU => (mul_u(a, b) >> 32) as u32,
            IntOp::DivS => (a as i32).checked_div(b as i32)? as u32,
            IntOp::DivU => a.checked_div(b)?,
            IntOp::RemS => (a as i32).checked_rem(b as i32)? as u32,
            IntOp::RemU => a.checked_rem(b)?,

            IntOp::Eq => (a == b) as u32,
            IntOp::LtS => ((a as i32) < (b as i32)) as u32,
            IntOp::LtU => (a < b) as u32,

            IntOp::And => a & b,
            IntOp::Or => a | b,
            IntOp::Xor => a ^ b,

            IntOp::Shl => a.wrapping_shl(b),
            IntOp::ShrS => (a as i32).wrapping_shr(b) as u32,
            IntOp::ShrU => a.wrapping_shr(b),
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
            (Ok(x), Err(other)) | (Err(other), Ok(x)) => match (self, x.sext32()) {
                (IntOp::Add, 0)
                | (IntOp::MulS, 1)
                | (IntOp::MulU, 1)
                | (IntOp::And, -1)
                | (IntOp::Or, 0)
                | (IntOp::Xor, 0) => return Some(Err(other)),

                (IntOp::MulS, 0)
                | (IntOp::MulU, 0)
                | (IntOp::MulHiS, 0)
                | (IntOp::MulHiU, 0)
                | (IntOp::And, 0)
                | (IntOp::Or, -1) => return Some(Ok(x)),

                _ => {}
            },
            _ => {}
        }

        // Asymmetric ops.
        match (a, b) {
            (Ok(a), Err(_)) => match (a.sext32(), self) {
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

            (Err(a), Ok(b)) => match (self, b.sext32()) {
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
    pub name: Option<&'static str>,
}

impl fmt::Debug for Reg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.name {
            Some(name) => write!(f, "{}", name),
            None => write!(f, "r{}", self.index),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum MemSize {
    M8,
    M16,
    M32,
}

impl Into<BitSize> for MemSize {
    fn into(self) -> BitSize {
        match self {
            MemSize::M8 => BitSize::B8,
            MemSize::M16 => BitSize::B16,
            MemSize::M32 => BitSize::B32,
        }
    }
}

impl MemSize {
    fn bits(self) -> u8 {
        match self {
            MemSize::M8 => 8,
            MemSize::M16 => 16,
            MemSize::M32 => 32,
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

    pub fn bit_not<P>(v: Use<Val>) -> impl AllocIn<Cx<P>, Kind = Self> {
        move |cx: &mut Cx<P>| {
            let size = cx[v].size();
            Val::Int(IntOp::Xor, size, v, cx.a(Const::new(size, size.mask())))
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
                            return Ok(Val::Int(IntOp::Add, size, a, cx.a(xy)));
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
                self = Val::Const(Const::new(size, c.zext32() & size.mask()));
            }
        }

        if let Val::Sext(size, x) = self {
            let x_size = cx[x].size();
            assert!(size > x_size);

            if let Some(c) = cx[x].as_const() {
                self = Val::Const(Const::new(size, (c.sext32() as u32) & size.mask()));
            }
        }

        if let Val::Zext(size, x) = self {
            let x_size = cx[x].size();
            assert!(size > x_size);

            if let Some(c) = cx[x].as_const() {
                self = Val::Const(Const::new(size, c.zext32()));
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

    pub fn guess_load<P>(&self, cx: &Cx<P>, addr: Use<Val>, size: MemSize) -> Option<Use<Val>> {
        if let Mem::Store(r, v) = *self {
            if r.addr == addr && r.size == size {
                Some(v)
            } else {
                cx[r.mem].guess_load(cx, addr, size)
            }
        } else {
            None
        }
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
    Branch {
        cond: Use<Val>,
        t: Use<Val>,
        e: Use<Val>,
    },

    PlatformCall {
        code: u32,
        ret_pc: Const,
    },
    Trap {
        code: u32,
    },
}

impl fmt::Debug for Effect {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Effect::Jump(target) => write!(f, "-> {:?}", target),
            Effect::Branch { cond, t, e } => write!(f, "-> {:?} ? {:?} : {:?}", cond, t, e),
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
            Effect::Branch { cond, t, e } => {
                visitor.visit_val_use(cond);
                visitor.visit_val_use(t);
                visitor.visit_val_use(e);
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

pub struct Block {
    pub pc: RangeTo<Const>,
    pub state: RangeTo<State>,
    pub effect: Effect,
}

pub trait Arch: Sized {
    fn default_regs(cx: &mut Cx<impl Platform<Arch = Self>>) -> Vec<Use<Val>>;

    fn lift_instr(
        cx: &mut Cx<impl Platform<Arch = Self>>,
        pc: &mut Const,
        state: &mut State,
    ) -> Option<Effect>;
}

#[derive(Debug)]
pub struct UnsupportedAddress(pub Const);

pub trait Rom {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress>;
}

pub trait Platform {
    type Arch: Arch;
    type Rom: Rom;

    fn arch(&self) -> &Self::Arch;
    fn rom(&self) -> &Self::Rom;
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
        principal: &'a (impl Visit + fmt::Debug),
        state: Option<&'a State>,
    ) -> impl fmt::Display + 'a {
        struct Data {
            named_refcounts: PerKind<HashMap<Use<Val>, usize>, HashMap<Use<Mem>, usize>>,
            locals: PerKind<
                HashMap<Use<Val>, Result<usize, Val>>,
                HashMap<Use<Mem>, Result<usize, Mem>>,
            >,
            val_to_state_regs: HashMap<Use<Val>, Vec<Reg>>,
            state_mem: Option<Use<Mem>>,
        }

        struct Collector<'a, P> {
            cx: &'a Cx<P>,
            data: Data,
        }

        impl<P> Visitor for Collector<'_, P> {
            type Platform = P;

            fn cx(&self) -> &Cx<Self::Platform> {
                self.cx
            }

            fn visit_val_use(&mut self, v: Use<Val>) {
                // FIXME(eddyb) skip entire already-visited subtrees.
                v.walk(self);

                self.data.locals.val.entry(v).or_insert(match self.cx[v] {
                    v @ Val::InReg(_) | v @ Val::Const(_) => Err(v),
                    _ => Ok({
                        let next = self.data.named_refcounts.val.len();
                        *self.data.named_refcounts.val.entry(v).or_insert(0) += 1;
                        next
                    }),
                });
            }
            fn visit_mem_use(&mut self, m: Use<Mem>) {
                // FIXME(eddyb) skip entire already-visited subtrees.
                m.walk(self);

                self.data.locals.mem.entry(m).or_insert(match self.cx[m] {
                    m @ Mem::In => Err(m),
                    _ => Ok({
                        let next = self.data.named_refcounts.mem.len();
                        *self.data.named_refcounts.mem.entry(m).or_insert(0) += 1;
                        next
                    }),
                });
            }
        }

        struct Printer<'a, P, F> {
            cx: &'a Cx<P>,
            data: &'a Data,
            fmt: &'a mut F,
            seen: PerKind<HashSet<Use<Val>>, HashSet<Use<Mem>>>,
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
                            let _ = write!(self.fmt, "    ");
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
                if let Some(&total) = self.data.named_refcounts.val.get(&v) {
                    if names < total {
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
                            let _ = write!(self.fmt, "    ");
                        }
                        let _ = write!(self.fmt, concat!($fmt_str, " = ") $($rest)*);
                        names += 1;
                    }}
                }

                if Some(m) == self.data.state_mem {
                    write_name!("m");
                }
                if let Some(&total) = self.data.named_refcounts.mem.get(&m) {
                    if names < total {
                        write_name!("{:?}", m);
                    }
                }
                if names > 0 {
                    let _ = writeln!(self.fmt, "{:?};", self.cx[m]);
                }
            }
        }

        let mut collector = Collector {
            cx: self,
            data: Data {
                named_refcounts: Default::default(),
                locals: Default::default(),
                val_to_state_regs: Default::default(),
                state_mem: None,
            },
        };
        if let Some(state) = state {
            if state.mem != self.default.mem {
                collector.data.state_mem = Some(state.mem);
            }

            for (i, &v) in state.regs.iter().enumerate() {
                let default = self.default.regs[i];
                if v == default {
                    continue;
                }

                // HACK(eddyb) try to guess the register name.
                // Ideally this would be provided by the `Arch`.
                let r = match self[default] {
                    Val::InReg(r) if i == r.index => r,
                    default => Reg {
                        index: i,
                        size: default.size(),
                        name: None,
                    },
                };
                collector
                    .data
                    .val_to_state_regs
                    .entry(v)
                    .or_default()
                    .push(r)
            }

            state.visit(&mut collector);
        }
        principal.visit(&mut collector);

        struct PrintFromDisplay<'a, P, T> {
            cx: &'a Cx<P>,
            data: Data,

            principal: &'a T,
            state: Option<&'a State>,
        }

        impl<P, T> fmt::Display for PrintFromDisplay<'_, P, T>
        where
            T: Visit + fmt::Debug,
        {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                writeln!(f, "{{")?;
                DBG_LOCALS.set(&self.data.locals, || {
                    // FIXME(eddyb) proper error-handling.
                    let mut printer = Printer {
                        cx: self.cx,
                        data: &self.data,
                        fmt: f,
                        seen: Default::default(),
                    };
                    if let Some(state) = self.state {
                        state.visit(&mut printer);
                    }
                    self.principal.visit(&mut printer);

                    writeln!(f, "    {:?}", self.principal)
                })?;
                write!(f, "}}")
            }
        }

        PrintFromDisplay {
            cx: self,
            data: collector.data,

            principal,
            state,
        }
    }
}

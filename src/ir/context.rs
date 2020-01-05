use crate::ir::{Node, Reg};
use elsa::FrozenVec;
use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::TryInto;
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;

pub struct Cx {
    interners: Interners,
}

/// Dispatch helper, to allow implementing interning logic on
/// the type passed to `cx.a(...)`.
pub trait InternInCx {
    type Interned;

    fn intern_in_cx(self, cx: &Cx) -> Self::Interned;
}

// FIXME(eddyb) is this sort of thing even needed anymore?
impl<T: InternInCx<Interned = INode>, F: FnOnce(&Cx) -> T> InternInCx for F {
    type Interned = INode;

    fn intern_in_cx(self, cx: &Cx) -> INode {
        self(cx).intern_in_cx(cx)
    }
}

impl Cx {
    pub fn new() -> Self {
        Cx {
            interners: Interners::default(),
        }
    }

    // FIXME(eddyb) rename this to `intern`.
    pub fn a<T: InternInCx>(&self, x: T) -> T::Interned {
        x.intern_in_cx(self)
    }
}

struct Interner<T: ?Sized> {
    // FIXME(Manishearth/elsa#6) switch to `FrozenIndexSet` when available.
    map: RefCell<HashMap<Rc<T>, u32>>,
    vec: FrozenVec<Rc<T>>,
}

impl<T: ?Sized + Eq + Hash> Default for Interner<T> {
    fn default() -> Self {
        Interner {
            map: RefCell::new(HashMap::default()),
            vec: FrozenVec::new(),
        }
    }
}

impl<T: ?Sized + Eq + Hash> Interner<T> {
    fn intern(&self, value: impl AsRef<T> + Into<Rc<T>>) -> u32 {
        if let Some(&i) = self.map.borrow().get(value.as_ref()) {
            return i;
        }
        let value = value.into();
        let next = self.vec.len().try_into().unwrap();
        self.map.borrow_mut().insert(value.clone(), next);
        self.vec.push(value);
        next
    }
}

macro_rules! interners {
    ($($name:ident => $ty:ty),* $(,)?) => {
        #[allow(non_snake_case)]
        #[derive(Default)]
        struct Interners {
            $($name: Interner<$ty>),*
        }

        $(
            #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub struct $name(u32);

            impl std::ops::Index<$name> for Cx {
                type Output = $ty;

                fn index(&self, interned: $name) -> &Self::Output {
                    &self.interners.$name.vec[interned.0 as usize]
                }
            }
        )*
    };
}

interners! {
    IReg => Reg,
    INode => Node,
}

// FIXME(eddyb) automate this away somehow.
impl AsRef<Self> for Reg {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl InternInCx for Reg {
    type Interned = IReg;
    fn intern_in_cx(self, cx: &Cx) -> IReg {
        IReg(cx.interners.IReg.intern(self))
    }
}

impl fmt::Debug for IReg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if super::DBG_CX.is_set() {
            super::DBG_CX.with(|cx| write!(f, "{:?}", &cx[*self]))
        } else {
            write!(f, "reg#{:x}", self.0)
        }
    }
}

// FIXME(eddyb) automate this away somehow.
impl AsRef<Self> for Node {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl InternInCx for Node {
    type Interned = INode;
    fn intern_in_cx(self, cx: &Cx) -> INode {
        match self.normalize(cx) {
            Ok(x) => INode(cx.interners.INode.intern(x)),
            Err(x) => x,
        }
    }
}

impl fmt::Debug for INode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let local = if super::DBG_LOCALS.is_set() {
            super::DBG_LOCALS.with(|locals| locals.get(self).copied())
        } else {
            None
        };
        match local {
            Some((prefix, i)) => write!(f, "{}{}", prefix, i),
            None => {
                if super::DBG_CX.is_set() {
                    super::DBG_CX.with(|cx| write!(f, "{:?}", &cx[*self]))
                } else {
                    write!(f, "node#{:x}", self.0)
                }
            }
        }
    }
}

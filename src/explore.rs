use crate::ir::{
    Arch, BitSize, Block, Const, Cx, Effect, MemSize, Platform, State, Use, Val, Visit, Visitor,
};
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap};
use std::fmt;

#[derive(Copy, Clone, Debug)]
enum Set1<T> {
    Empty,
    One(T),
    Many,
}

impl<T: Eq> Set1<T> {
    fn insert(&mut self, value: T) {
        match *self {
            Set1::Empty => *self = Set1::One(value),
            Set1::One(ref prev) if *prev == value => {}
            _ => *self = Set1::Many,
        }
    }

    fn union(mut self, other: Self) -> Self {
        match other {
            Set1::Empty => {}
            Set1::One(x) => self.insert(x),
            Set1::Many => return Set1::Many,
        }
        self
    }

    fn flat_map(self, f: impl FnOnce(T) -> Self) -> Self {
        match self {
            Set1::Empty | Set1::Many => self,
            Set1::One(x) => f(x),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId {
    pub entry_pc: u64,
}

impl fmt::Debug for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Const::new(BitSize::B64, self.entry_pc).fmt(f)
    }
}

impl From<Const> for BlockId {
    fn from(entry_pc: Const) -> Self {
        BlockId {
            entry_pc: entry_pc.as_u64(),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum ReducedVal {
    Simple(Use<Val>),
    Load { addr: Use<Val>, size: MemSize },
}

impl Visit for ReducedVal {
    fn walk(&self, visitor: &mut impl Visitor) {
        match *self {
            ReducedVal::Simple(val) => visitor.visit_val_use(val),
            ReducedVal::Load { addr, .. } => visitor.visit_val_use(addr),
        }
    }
}

impl ReducedVal {
    fn subst<P>(mut self, cx: &mut Cx<P>, base: &State) -> Self {
        self = match self {
            ReducedVal::Simple(val) => ReducedVal::Simple(val.subst(cx, base)),
            ReducedVal::Load { addr, size } => ReducedVal::Load {
                addr: addr.subst(cx, base),
                size,
            },
        };

        // HACK(eddyb) try to get the last stored value.
        loop {
            let (mem, addr, size) = match self {
                ReducedVal::Simple(val) => match cx[val] {
                    Val::Load(r) => (r.mem, r.addr, r.size),
                    _ => break,
                },
                ReducedVal::Load { addr, size } => (base.mem, addr, size),
            };
            match cx[mem].guess_load(cx, addr, size) {
                Some(v) => self = ReducedVal::Simple(v),
                None => {
                    // Replace `ReducedVal::Simple(Load(_))` with
                    // `ReducedVal::Load`, to ignore the base memory.
                    self = ReducedVal::Load { addr, size };
                    break;
                }
            }
        }

        self
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct DynTarget {
    val: ReducedVal,

    /// The number of dynamic jumps this target
    /// was found behind.
    /// E.g. for `x: call a; y: call b; z: ret`,
    /// assuming `a` and `b` are leaf functions,
    /// the `ret` target has depth `0` at `z`,
    /// `1` at `y` and `2` at `x`.
    depth: u32,
}

impl Visit for DynTarget {
    fn walk(&self, visitor: &mut impl Visitor) {
        self.val.visit(visitor);
    }
}

#[derive(Copy, Clone)]
struct Cyclic;

pub struct Explorer<'a, P> {
    pub cx: &'a mut Cx<P>,
    pub blocks: BTreeMap<BlockId, Block>,

    dyn_target_cache: HashMap<(Option<DynTarget>, BlockId), Result<Set1<DynTarget>, Cyclic>>,
}

impl<'a, P: Platform> Explorer<'a, P> {
    pub fn new(cx: &'a mut Cx<P>) -> Self {
        Explorer {
            cx,
            blocks: BTreeMap::new(),
            dyn_target_cache: HashMap::new(),
        }
    }

    pub fn get_or_lift_block(&mut self, bb: BlockId) -> &Block {
        // FIXME(eddyb) clean this up whenever NLL/Polonius can do the
        // efficient check (`if let Some(x) = map.get(k) { return x; }`).
        if !self.blocks.contains_key(&bb) {
            let mut state = self.cx.default.clone();
            let mut pc = Const::new(P::Arch::ADDR_SIZE, bb.entry_pc);
            let effect = loop {
                match P::Arch::lift_instr(self.cx, &mut pc, &mut state) {
                    Some(effect) => break effect,
                    None => {}
                }

                // Prevent blocks from overlapping where possible.
                if self.blocks.contains_key(&BlockId::from(pc)) {
                    break Effect::Jump(self.cx.a(pc));
                }
            };

            self.blocks.insert(
                bb,
                Block {
                    pc: ..pc,
                    state: ..state,
                    effect,
                },
            );
        }
        &self.blocks[&bb]
    }

    pub fn explore_bbs(&mut self, entry_pc: Const) {
        let entry_bb = BlockId::from(entry_pc);

        loop {
            let num_blocks = self.blocks.len();
            let (dyn_targets, _) = self.bb_dyn_targets(None, entry_bb);
            if let Set1::One(target) = dyn_targets {
                println!(
                    "explore: entry {:?} reaches unknown target {}",
                    entry_bb,
                    self.cx.pretty_print(&target, None)
                );
            }

            // TODO(eddyb) split blocks that overlap other blocks.

            if self.blocks.len() == num_blocks {
                break;
            }
            self.dyn_target_cache.clear();
        }
    }

    // FIXME(eddyb) reuse cached value when it doesn't interact with `replacement`.
    fn bb_dyn_targets(
        &mut self,
        replacement: Option<DynTarget>,
        bb: BlockId,
    ) -> (Set1<DynTarget>, Option<Cyclic>) {
        match self.dyn_target_cache.entry((replacement, bb)) {
            Entry::Occupied(entry) => {
                let r = entry.get();
                return (r.unwrap_or(Set1::Empty), r.err());
            }
            Entry::Vacant(entry) => {
                entry.insert(Err(Cyclic));
            }
        }

        let effect = self.get_or_lift_block(bb).effect;
        let mut dyn_targets_of_target = |target: Use<Val>| {
            if let Some(target_bb) = self.cx[target].as_const().map(BlockId::from) {
                let (mut dyn_targets, cyclic) = self.bb_dyn_targets(replacement, target_bb);

                if let Set1::One(target) = &mut dyn_targets {
                    target.val = target.val.subst(self.cx, &self.blocks[&bb].state.end);
                }

                (dyn_targets, cyclic)
            } else {
                let target = match replacement {
                    Some(DynTarget { val, depth: 0 }) => {
                        val.subst(self.cx, &self.blocks[&bb].state.end)
                    }
                    _ => ReducedVal::Simple(target),
                };
                (
                    Set1::One(DynTarget {
                        val: target,
                        depth: 0,
                    }),
                    None,
                )
            }
        };
        let (mut dyn_targets, mut cyclic) = match effect {
            Effect::Jump(target) => dyn_targets_of_target(target),
            Effect::Branch { t, e, .. } => {
                let (mut t_dyn_targets, t_cyclic) = dyn_targets_of_target(t);
                let (mut e_dyn_targets, e_cyclic) = dyn_targets_of_target(e);
                if let (Set1::One(t), Set1::One(e)) = (&mut t_dyn_targets, &mut e_dyn_targets) {
                    if t.val == e.val && t.depth != e.depth {
                        let depth = t.depth.max(e.depth);
                        println!(
                            "explore: {:?}: mismatched depth: {} vs {}, picking {}",
                            bb, t.depth, e.depth, depth,
                        );
                        t.depth = depth;
                        e.depth = depth;
                    }
                    if t != e {
                        println!(
                            "explore: {:?}: ambiguous dyn targets: {} vs {}",
                            bb,
                            self.cx.pretty_print(&*t, None),
                            self.cx.pretty_print(&*e, None)
                        );
                    }
                }
                (t_dyn_targets.union(e_dyn_targets), t_cyclic.or(e_cyclic))
            }
            Effect::PlatformCall { ret_pc, .. } => {
                self.bb_dyn_targets(replacement, BlockId::from(ret_pc))
            }
            Effect::Trap { .. } => (Set1::Empty, None),
        };

        // Propagate the value backwards through this BB.
        if let Set1::One(target) = dyn_targets {
            let const_target = match target.val {
                ReducedVal::Simple(val) => self.cx[val].as_const(),
                _ => None,
            };
            if let Some(target_bb) = const_target.map(BlockId::from) {
                // Recurse on the indirect target.
                let target_replacement = replacement.and_then(|DynTarget { val, depth }| {
                    if depth == target.depth {
                        panic!(
                            "explore: {:?} -> {:?} still constant after having been replaced",
                            bb, target
                        );
                    }
                    depth
                        .checked_sub(target.depth + 1)
                        .map(|depth| DynTarget { val, depth })
                });
                let (target_target, target_cyclic) =
                    self.bb_dyn_targets(target_replacement, target_bb);
                cyclic = cyclic.or(target_cyclic);
                dyn_targets = target_target.flat_map(|target_target| {
                    // Recompute the current BB, replacing the target with
                    // the target BB's target, to get the final target.
                    let (final_target, final_cyclic) = self.bb_dyn_targets(
                        Some(DynTarget {
                            val: target_target.val,
                            depth: target.depth,
                        }),
                        bb,
                    );
                    cyclic = cyclic.or(final_cyclic);
                    final_target.flat_map(|final_target| {
                        assert_eq!(target.depth, final_target.depth);
                        Set1::One(DynTarget {
                            val: final_target.val,
                            depth: target.depth + target_target.depth + 1,
                        })
                    })
                });
            }
        }

        // Cycles are irrelevant if we're already dealing with more than one value.
        if let Set1::Many = dyn_targets {
            cyclic = None;
        }

        // Only cache results not tainted by cycles.
        if cyclic.is_none() {
            self.dyn_target_cache
                .insert((replacement, bb), Ok(dyn_targets));
        }

        (dyn_targets, cyclic)
    }
}

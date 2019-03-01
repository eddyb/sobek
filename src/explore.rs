use crate::ir::{
    Arch, BitSize, Block, Const, Cx, Effect, MemSize, Platform, State, Use, Val, Visit, Visitor,
};
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap};
use std::{fmt, mem};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

    fn map<U>(self, f: impl FnOnce(T) -> U) -> Set1<U> {
        match self {
            Set1::Empty => Set1::Empty,
            Set1::Many => Set1::Many,
            Set1::One(x) => Set1::One(f(x)),
        }
    }

    fn flat_map<U>(self, f: impl FnOnce(T) -> Set1<U>) -> Set1<U> {
        match self {
            Set1::Empty => Set1::Empty,
            Set1::Many => Set1::Many,
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

/// Options for handling an exit "continuation".
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
struct ExitOptions {
    /// Argument value for the exit "continuation".
    /// If present, will be back-propagated from
    /// all the jumps to the exit "continuation".
    arg_value: Option<ReducedVal>,
}

struct Partial {
    /// Set to `true` when a cached partial value is used.
    observed: bool,
}

/// The cumulative exit "continuation" of a (sub-)CFG,
/// computed from all the jumps that don't resolve to
/// a static target.
struct Exit {
    /// Set of non-constant jump destination values.
    /// An empty set indicates the (sub-)CFG diverges, by
    /// eventually reaching infinite loops and/or traps.
    targets: Set1<ReducedVal>,

    /// Set of "continuation argument" values.
    /// Only empty if no argument was provided (see `ExitKey`).
    // TODO(eddyb) should this be per `targets` value?
    arg_values: Set1<ReducedVal>,

    /// Indicates whether this (sub-)CFG contains unresolved
    /// cycles, which may have resulted in the computed exit
    /// being different from the eventual fixpoint.
    partial: Option<Partial>,
}

impl Exit {
    fn merge(self, other: Self) -> Self {
        Exit {
            targets: self.targets.union(other.targets),
            arg_values: self.arg_values.union(other.arg_values),
            partial: self.partial.or(other.partial),
        }
    }

    fn subst<P>(self, cx: &mut Cx<P>, base: &State) -> Self {
        Exit {
            targets: self.targets.map(|target| target.subst(cx, base)),
            arg_values: self.arg_values.map(|arg_value| arg_value.subst(cx, base)),
            partial: self.partial,
        }
    }
}

pub struct Explorer<'a, P> {
    pub cx: &'a mut Cx<P>,
    pub blocks: BTreeMap<BlockId, Block>,

    exit_cache: HashMap<(BlockId, ExitOptions), Exit>,
}

impl<'a, P: Platform> Explorer<'a, P> {
    pub fn new(cx: &'a mut Cx<P>) -> Self {
        Explorer {
            cx,
            blocks: BTreeMap::new(),
            exit_cache: HashMap::new(),
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
            let exit = self.find_exit(entry_bb, ExitOptions::default());
            exit.targets.map(|target| {
                println!(
                    "explore: entry {:?} reaches unknown exit target {}",
                    entry_bb,
                    self.cx.pretty_print(&target, None)
                );
            });

            // TODO(eddyb) split blocks that overlap other blocks.

            if self.blocks.len() == num_blocks {
                break;
            }
            self.exit_cache.clear();
        }
    }

    fn find_exit_uncached_from_effect(&mut self, bb: BlockId, options: ExitOptions) -> Exit {
        let effect = self.get_or_lift_block(bb).effect;
        let mut exit_from_target = |target: Use<Val>| {
            if let Some(target_bb) = self.cx[target].as_const().map(BlockId::from) {
                self.find_exit(target_bb, options)
                    .subst(self.cx, &self.blocks[&bb].state.end)
            } else {
                Exit {
                    targets: Set1::One(ReducedVal::Simple(target)),
                    arg_values: options.arg_value.map_or(Set1::Empty, |arg_value| {
                        Set1::One(arg_value.subst(self.cx, &self.blocks[&bb].state.end))
                    }),
                    partial: None,
                }
            }
        };
        match effect {
            Effect::Jump(target) => exit_from_target(target),
            Effect::Branch { t, e, .. } => {
                let t_exit = exit_from_target(t);
                let e_exit = exit_from_target(e);
                if let (Set1::One(t), Set1::One(e)) = (t_exit.targets, e_exit.targets) {
                    if t != e {
                        println!(
                            "explore: {:?}: ambiguous targets: {} vs {}",
                            bb,
                            self.cx.pretty_print(&t, None),
                            self.cx.pretty_print(&e, None)
                        );
                    }
                }
                t_exit.merge(e_exit)
            }
            Effect::PlatformCall { ret_pc, .. } => self.find_exit(BlockId::from(ret_pc), options),
            Effect::Trap { .. } => Exit {
                targets: Set1::Empty,
                arg_values: Set1::Empty,
                partial: None,
            },
        }
    }

    fn find_exit_uncached(&mut self, bb: BlockId, options: ExitOptions) -> Exit {
        let Exit {
            mut targets,
            mut arg_values,
            mut partial,
        } = self.find_exit_uncached_from_effect(bb, options);

        if let Set1::One(target) = targets {
            let const_target = match target {
                ReducedVal::Simple(val) => self.cx[val].as_const(),
                _ => None,
            };
            if let Some(target_bb) = const_target.map(BlockId::from) {
                // FIXME(eddyb) abstract this better wrt `Exit` / `partial`.

                // Recurse on the indirect target.
                let target_exit = self.find_exit(target_bb, options);
                partial = partial.or(target_exit.partial);
                let mut resolve_values = |values: Set1<ReducedVal>| {
                    values.flat_map(|value| {
                        // Reuse the already computed `arg_values` where possible.
                        if Some(value) == options.arg_value {
                            return arg_values;
                        }

                        let exit = self.find_exit_uncached_from_effect(
                            bb,
                            ExitOptions {
                                arg_value: Some(value),
                            },
                        );
                        partial = partial.take().or(exit.partial);
                        exit.arg_values
                    })
                };
                targets = resolve_values(target_exit.targets);
                arg_values = resolve_values(target_exit.arg_values);
            }
        }

        // Cycles are irrelevant if we're already fully general.
        if let Set1::Many = targets {
            partial = None;
        }

        Exit {
            targets,
            arg_values,
            partial,
        }
    }

    // FIXME(eddyb) reuse cached value when it doesn't interact with `options`.
    fn find_exit(&mut self, bb: BlockId, options: ExitOptions) -> Exit {
        match self.exit_cache.entry((bb, options)) {
            Entry::Occupied(mut entry) => {
                let cached = entry.get_mut();
                return Exit {
                    targets: cached.targets,
                    arg_values: cached.arg_values,
                    partial: cached.partial.as_mut().map(|partial| {
                        partial.observed = true;
                        Partial { observed: false }
                    }),
                };
            }
            Entry::Vacant(entry) => {
                entry.insert(Exit {
                    targets: Set1::Empty,
                    arg_values: Set1::Empty,
                    partial: Some(Partial { observed: false }),
                });
            }
        }

        // TODO(eddyb) actually show that retrying `find_exit_uncached`
        // has *any* effect on the overall results!
        // It *might* be the case that not caching a partial value
        // (i.e. the `entry.remove()` call) has a similar effect?
        loop {
            let exit = self.find_exit_uncached(bb, options);

            let mut entry = match self.exit_cache.entry((bb, options)) {
                Entry::Occupied(entry) => entry,
                Entry::Vacant(_) => unreachable!(),
            };
            let cached = entry.get_mut();
            let old_targets = mem::replace(&mut cached.targets, exit.targets);
            let old_arg_values = mem::replace(&mut cached.arg_values, exit.arg_values);
            let old_observed = mem::replace(&mut cached.partial.as_mut().unwrap().observed, false);

            // Keep retrying as long as a now-obsolete `targets` / `arg_values` was observed.
            // TODO(eddyb) how should fixpoint be detected?
            // Can't assume that a certain `targets` set is final,
            // as there could be outer cycles blocking progress.
            if old_observed && (old_targets != exit.targets || old_arg_values != exit.arg_values) {
                continue;
            }

            // Only cache final results.
            if let Some(partial) = &exit.partial {
                // The `observed` flag should only ever be set for
                // the `Exit` inside the cache, but nothing else.
                assert_eq!(partial.observed, false);

                entry.remove();
            } else {
                cached.partial.take();
            }

            return exit;
        }
    }
}

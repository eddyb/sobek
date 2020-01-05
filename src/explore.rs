use crate::ir::{
    BitSize, Block, Const, Cx, Edge, Edges, Effect, INode, MemRef, MemSize, Node, State, Visit,
    Visitor,
};
use crate::platform::{Platform, Rom};
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicBool, Ordering};
use std::{fmt, mem};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Set1<T> {
    Empty,
    One(T),
    Many,
}

impl<T: Visit> Visit for Set1<T> {
    fn walk(&self, visitor: &mut impl Visitor) {
        match self {
            Set1::Empty | Set1::Many => {}
            Set1::One(x) => x.visit(visitor),
        }
    }
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
            Set1::One(x) => Set1::One(f(x)),
            Set1::Many => Set1::Many,
        }
    }

    fn flat_map<U>(self, f: impl FnOnce(T) -> Set1<U>) -> Set1<U> {
        match self {
            Set1::Empty => Set1::Empty,
            Set1::One(x) => f(x),
            Set1::Many => Set1::Many,
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

impl INode {
    // HACK(eddyb) try to get the last stored value.
    fn subst_reduce_load(
        self,
        cx: &Cx,
        rom: &dyn Rom,
        base: Option<&State>,
        addr: INode,
        size: MemSize,
    ) -> INode {
        match cx[self] {
            Node::InMem => match base {
                Some(base) => base.mem.subst_reduce_load(cx, rom, None, addr, size),
                None => {
                    // HACK(eddyb) assume it's from the ROM, if in range of it.
                    if let Some(addr) = cx[addr].as_const() {
                        if let Ok(v) = rom.load(addr, size) {
                            return cx.a(v);
                        }
                    }

                    cx.a(Node::Load(MemRef {
                        mem: self,
                        addr,
                        size,
                    }))
                }
            },

            Node::Store(r, v) => {
                if r.addr.subst_reduce(cx, rom, base) == addr && r.size == size {
                    v.subst_reduce(cx, rom, base)
                } else {
                    r.mem.subst_reduce_load(cx, rom, base, addr, size)
                }
            }

            _ => unreachable!(),
        }
    }
}

// FIXME(eddyb) introduce a more general "folder" abstraction.
impl INode {
    fn subst_reduce(self, cx: &Cx, rom: &dyn Rom, base: Option<&State>) -> Self {
        cx.a(match cx[self] {
            Node::InReg(r) => {
                return base.map_or(self, |base| {
                    base.regs[cx[r].index].subst_reduce(cx, rom, None)
                })
            }

            Node::Const(_) => return self,

            Node::Int(op, size, a, b) => Node::Int(
                op,
                size,
                a.subst_reduce(cx, rom, base),
                b.subst_reduce(cx, rom, base),
            ),
            Node::Trunc(size, x) => Node::Trunc(size, x.subst_reduce(cx, rom, base)),
            Node::Sext(size, x) => Node::Sext(size, x.subst_reduce(cx, rom, base)),
            Node::Zext(size, x) => Node::Zext(size, x.subst_reduce(cx, rom, base)),
            Node::Load(r) => {
                let addr = r.addr.subst_reduce(cx, rom, base);
                return r.mem.subst_reduce_load(cx, rom, base, addr, r.size);
            }

            Node::InMem => return base.map_or(self, |base| base.mem.subst_reduce(cx, rom, None)),

            Node::Store(r, x) => Node::Store(
                MemRef {
                    mem: r.mem.subst_reduce(cx, rom, base),
                    addr: r.addr.subst_reduce(cx, rom, base),
                    size: r.size,
                },
                x.subst_reduce(cx, rom, base),
            ),
        })
    }
}

/// Options for handling an exit "continuation".
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
struct ExitOptions {
    /// Argument value for the exit "continuation".
    /// If present, will be back-propagated from
    /// all the jumps to the exit "continuation".
    arg_value: Option<INode>,
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
    targets: Set1<INode>,

    /// Set of "continuation argument" values.
    /// Only empty if no argument was provided (see `ExitKey`).
    // TODO(eddyb) should this be per `targets` value?
    arg_values: Set1<INode>,

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
}

pub struct Explorer<'a> {
    pub cx: &'a Cx,
    pub platform: &'a dyn Platform,
    pub blocks: BTreeMap<BlockId, Block>,

    /// Analysis output indicating that a block takes a "continuation" which is
    /// static in some ancestors, e.g. callees taking the return "continuation".
    pub takes_static_continuation: HashSet<BlockId>,

    /// Analysis output indicating that a block will eventually reach another
    /// block by going through some sub-CFG that takes a "continuation",
    /// e.g. calls reaching the return "continuation".
    pub eventual_static_continuation: HashMap<BlockId, BlockId>,

    cancel_token: Option<&'a AtomicBool>,

    exit_cache: HashMap<(BlockId, ExitOptions), Exit>,
}

impl<'a> Explorer<'a> {
    pub fn new(
        cx: &'a Cx,
        platform: &'a dyn Platform,
        cancel_token: Option<&'a AtomicBool>,
    ) -> Self {
        Explorer {
            cx,
            platform,
            blocks: BTreeMap::new(),
            takes_static_continuation: HashSet::new(),
            eventual_static_continuation: HashMap::new(),
            cancel_token,
            exit_cache: HashMap::new(),
        }
    }

    pub fn get_or_lift_block(&mut self, bb: BlockId) -> &Block {
        // FIXME(eddyb) clean this up whenever NLL/Polonius can do the
        // efficient check (`if let Some(x) = map.get(k) { return x; }`).
        while !self.blocks.contains_key(&bb) {
            let reg_defs: Vec<_> = self
                .platform
                .isa()
                .regs()
                .into_iter()
                .map(|r| self.cx.a(r))
                .collect();
            let mut state = State {
                mem: self.cx.a(Node::InMem),
                regs: reg_defs
                    .iter()
                    .map(|&r| self.cx.a(Node::InReg(r)))
                    .collect(),
                reg_defs,
            };
            let mut pc = Const::new(self.platform.isa().addr_size(), bb.entry_pc);
            let edges = loop {
                match self
                    .platform
                    .isa()
                    .lift_instr(self.cx, self.platform.rom(), &mut pc, state)
                {
                    Ok(new_state) => state = new_state,
                    Err(edges) => break edges,
                }

                // Prevent blocks from overlapping where possible.
                if self.blocks.contains_key(&BlockId::from(pc)) {
                    break Edges::One(Edge {
                        state,
                        effect: Effect::Jump(self.cx.a(pc)),
                    });
                }
            };

            // HACK(eddyb) detect the simplest self-loops, and split the block.
            let retry = edges
                .as_ref()
                .map(|e, _| match e.effect {
                    Effect::Jump(target)
                    | Effect::Opaque {
                        next_pc: target, ..
                    } => self.cx[target]
                        .as_const()
                        .map(BlockId::from)
                        .filter(|&target| bb < target && target.entry_pc < pc.as_u64())
                        .map(|target| self.get_or_lift_block(target))
                        .is_some(),
                    Effect::Error(_) => false,
                })
                .merge(|a, b| a | b);
            if retry {
                continue;
            }

            self.blocks.insert(bb, Block { pc: ..pc, edges });
            break;
        }
        &self.blocks[&bb]
    }

    /// Split any blocks that overlap the block following them.
    /// Warning: this may invalidate analyses sensitive to the distinction.
    pub fn split_overlapping_bbs(&mut self) {
        let bb_range_after = |this: &Self, start: Option<BlockId>| {
            use std::ops::Bound::*;
            this.blocks
                .range((start.map_or(Unbounded, Excluded), Unbounded))
                .map(|(&bb, block)| bb..BlockId::from(block.pc.end))
                .next()
        };

        if let Some(mut bb) = bb_range_after(self, None) {
            while let Some(next) = bb_range_after(self, Some(bb.start)) {
                // Split overlapping blocks by discarding and re-lifting them.
                if bb.contains(&next.start) {
                    self.blocks.remove(&bb.start);
                    self.eventual_static_continuation.remove(&bb.start);
                    self.get_or_lift_block(bb.start);
                }

                bb = next;
            }
        }
    }

    pub fn explore_bbs(&mut self, entry_pc: Const) {
        let entry_bb = BlockId::from(entry_pc);

        let exit = self.find_exit(entry_bb, ExitOptions::default());
        exit.targets.map(|target| {
            println!(
                "explore: entry {:?} reaches unknown exit target {}",
                entry_bb,
                self.cx.pretty_print(&target)
            );
        });
    }

    fn find_exit_uncached_on_edge(
        &mut self,
        bb: BlockId,
        options: ExitOptions,
        br_cond: Option<bool>,
    ) -> Exit {
        let mut exit = match self
            .get_or_lift_block(bb)
            .edges
            .as_ref()
            .get(br_cond)
            .effect
        {
            Effect::Jump(direct_target)
            | Effect::Opaque {
                next_pc: direct_target,
                ..
            } => Exit {
                targets: Set1::One(direct_target.subst_reduce(self.cx, self.platform.rom(), None)),
                arg_values: options.arg_value.map_or(Set1::Empty, |arg_value| {
                    Set1::One(arg_value.subst_reduce(
                        self.cx,
                        self.platform.rom(),
                        Some(&self.blocks[&bb].edges.as_ref().get(br_cond).state),
                    ))
                }),
                partial: None,
            },
            Effect::Error(_) => {
                return Exit {
                    targets: Set1::Empty,
                    arg_values: Set1::Empty,
                    partial: None,
                }
            }
        };

        // HACK(eddyb) this uses a stack of targets to be able to handle a chain
        // of exit continuations, all resolved by `bb` simultaneously.
        // This can happen when e.g. there is a call in between a jump table
        // and a constant input to the jump table: the call will be the first
        // entry in the stack, followed by the jump table.
        let mut stack = vec![];
        loop {
            let target_bb = match exit
                .targets
                .map(|target| self.cx[target].as_const().map(BlockId::from))
            {
                Set1::One(Some(target_bb)) => target_bb,
                _ => return exit,
            };

            // HACK(eddyb) detect trivial fixpoints/cycles.
            if stack.last() == Some(&target_bb) {
                let arg_values_is_const = match exit.arg_values {
                    Set1::Empty | Set1::Many => true,
                    Set1::One(value) => self.cx[value].as_const().is_some(),
                };
                if arg_values_is_const {
                    exit.targets = Set1::Empty;
                    return exit;
                }
            }

            if let [prev_target_bb] = stack[..] {
                self.takes_static_continuation.insert(prev_target_bb);
                // HACK(eddyb) save the observed value without accounting
                // for multiple possible values etc.
                self.eventual_static_continuation.insert(bb, target_bb);
            }

            // Recurse on the current target.
            let target_exit = self.find_exit(target_bb, options);
            // FIXME(eddyb) abstract composing `partial`s better.
            exit.partial = exit.partial.or(target_exit.partial);
            let mut resolve_values = |values: Set1<INode>| {
                values.flat_map(|value| {
                    // Constants don't need any propagation work.
                    if self.cx[value].as_const().is_some() {
                        return Set1::One(value);
                    }

                    // Reuse the already computed `arg_values` where possible.
                    if Some(value) == options.arg_value {
                        return exit.arg_values;
                    }

                    let mut values = Set1::One(value);
                    for &frame_bb in stack.iter().rev() {
                        values = values.flat_map(|value| {
                            let frame_exit = self.find_exit(
                                frame_bb,
                                ExitOptions {
                                    arg_value: Some(value),
                                },
                            );
                            exit.partial = exit.partial.take().or(frame_exit.partial);
                            frame_exit.arg_values
                        });
                    }
                    values.map(|arg_value| {
                        arg_value.subst_reduce(
                            self.cx,
                            self.platform.rom(),
                            Some(&self.blocks[&bb].edges.as_ref().get(br_cond).state),
                        )
                    })
                })
            };

            let (targets, arg_values) = (
                resolve_values(target_exit.targets),
                resolve_values(target_exit.arg_values),
            );
            exit.targets = targets;
            exit.arg_values = arg_values;

            stack.push(target_bb);
        }
    }

    fn find_exit_uncached(&mut self, bb: BlockId, options: ExitOptions) -> Exit {
        let edges = self.get_or_lift_block(bb).edges.as_ref().map(|_, _| ());

        // TODO(eddyb) avoid duplicating work between the `t` and `e`
        // of a branch in `exit_from_target`, when they converge early.
        edges
            .map(|(), br_cond| self.find_exit_uncached_on_edge(bb, options, br_cond))
            .merge(|t, e| {
                if let (Set1::One(t), Set1::One(e)) = (t.targets, e.targets) {
                    if t != e {
                        println!(
                            "explore: {:?}: ambiguous targets: {} vs {}",
                            bb,
                            self.cx.pretty_print(&t),
                            self.cx.pretty_print(&e)
                        );
                    }
                }
                t.merge(e)
            })
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
            let mut exit = self.find_exit_uncached(bb, options);

            // HACK(eddyb) find a more principled place to stick this in.
            if let Some(cancel_token) = self.cancel_token {
                if cancel_token.load(Ordering::Relaxed) {
                    return exit;
                }
            }

            // Cycles are irrelevant if we're already fully general.
            if let Set1::Many = exit.targets {
                exit.partial = None;
            }

            let mut entry = match self.exit_cache.entry((bb, options)) {
                Entry::Occupied(entry) => entry,
                Entry::Vacant(_) => unreachable!(),
            };
            let cached = entry.get_mut();
            let old_targets = mem::replace(&mut cached.targets, exit.targets);
            let old_arg_values = mem::replace(&mut cached.arg_values, exit.arg_values);
            let old_observed = mem::replace(&mut cached.partial.as_mut().unwrap().observed, false);

            // Keep retrying as long as a now-obsolete `targets` / `arg_values` were observed.
            // TODO(eddyb) how should fixpoint be detected?
            // Can't assume that a certain `targets` set is final,
            // as there could be outer cycles blocking progress.
            let cx = self.cx;
            let progress = |old: Set1<INode>, new: Set1<INode>| match (old, new) {
                (Set1::One(old), Set1::One(new)) => {
                    if old != new {
                        println!(
                            "explore: {:?} changed a value from {} to {}",
                            bb,
                            cx.pretty_print(&old),
                            cx.pretty_print(&new)
                        )
                    }
                    false
                }
                (Set1::Empty, Set1::Empty) | (Set1::Many, Set1::Many) => false,
                (Set1::Empty, _) | (_, Set1::Many) => true,
                (_, Set1::Empty) | (Set1::Many, _) => unreachable!(),
            };
            // Always check for progress, to ensure the sanity checks run.
            let progress =
                progress(old_targets, exit.targets) | progress(old_arg_values, exit.arg_values);
            if old_observed && progress {
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

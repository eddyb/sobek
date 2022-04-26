use crate::ir::{
    BitSize, Block, Const, Cx, Edge, Edges, Effect, INode, IntOp, MemRef, MemSize, Node, State,
    Visit, Visitor,
};
use crate::platform::Platform;
use itertools::{Either, Itertools};
use smallvec::SmallVec;
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::io::Write;
use std::mem;
use std::sync::atomic::{AtomicBool, Ordering};
use std::{fmt, iter};

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

trait MaybeSet<T>: From<T> {
    fn maybe_set<I: IntoIterator<Item = T>>(_f: impl FnOnce() -> I) -> Option<Self> {
        None
    }
    fn flat_map(self, f: impl FnMut(T) -> Self) -> Self;
}

impl<T> MaybeSet<T> for T {
    fn flat_map(self, mut f: impl FnMut(T) -> Self) -> Self {
        f(self)
    }
}

// FIXME(eddyb) maybe use a library for this?
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SmallSet<T> {
    Empty,
    One(T),
    Many(BTreeSet<T>),
}

impl<T> From<T> for SmallSet<T> {
    fn from(x: T) -> Self {
        SmallSet::One(x)
    }
}

impl<T: Ord> SmallSet<T> {
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T> {
        match self {
            SmallSet::Empty => Either::Left(None.into_iter()),
            SmallSet::One(x) => Either::Left(Some(x).into_iter()),
            SmallSet::Many(set) => Either::Right(set.iter()),
        }
    }

    pub fn into_iter(self) -> impl Iterator<Item = T> {
        match self {
            SmallSet::Empty => Either::Left(None.into_iter()),
            SmallSet::One(x) => Either::Left(Some(x).into_iter()),
            SmallSet::Many(set) => Either::Right(set.into_iter()),
        }
    }

    fn insert(&mut self, value: T) {
        let prev = match self {
            SmallSet::Empty => {
                *self = SmallSet::One(value);
                return;
            }
            SmallSet::One(prev) if *prev == value => return,
            SmallSet::One(_) => match mem::replace(self, SmallSet::Many(BTreeSet::new())) {
                SmallSet::One(prev) => Some(prev),
                _ => unreachable!(),
            },
            SmallSet::Many(_) => None,
        };
        match self {
            SmallSet::Many(set) => {
                set.extend(prev);
                set.insert(value);
            }
            _ => unreachable!(),
        }
    }
}

impl<T: Ord> MaybeSet<T> for SmallSet<T> {
    fn maybe_set<I: IntoIterator<Item = T>>(f: impl FnOnce() -> I) -> Option<Self> {
        let mut set = SmallSet::Empty;
        for x in f().into_iter() {
            set.insert(x);
        }
        Some(set)
    }

    fn flat_map(self, mut f: impl FnMut(T) -> Self) -> Self {
        let mut result = SmallSet::Empty;
        for x in self.into_iter().map(|x| f(x).into_iter()).flatten() {
            result.insert(x);
        }
        result
    }
}

impl INode {
    // HACK(eddyb) try to get the last stored value.
    fn subst_reduce_load<S: MaybeSet<INode>>(
        self,
        explorer: &Explorer<'_>,
        base: Option<&State>,
        addr: INode,
        size: MemSize,
    ) -> S {
        let cx = explorer.cx;
        match cx[self] {
            Node::GlobalIn(g) => {
                if let Some(m) = base.and_then(|base| base.globals.get(&g).copied()) {
                    return m.subst_reduce_load(explorer, None, addr, size);
                }

                if g == explorer.platform.isa().mem_containing_rom() {
                    let mem_type = cx[g].ty.mem().unwrap();

                    // HACK(eddyb) assume it's from the ROM, if in range of it.
                    if let Some(addr) = cx[addr].as_const() {
                        if let Ok(v) = explorer.platform.rom().load(mem_type, addr, size) {
                            return cx.a(v).into();
                        }
                    }

                    // HACK(eddyb) assume that an array-like address has a
                    // first element (and notify the user about it).
                    if let Node::Int(IntOp::Add, _, index, base_addr) = cx[addr] {
                        if let Some(base_addr) = cx[base_addr].as_const() {
                            if let Some(&byte_len) = explorer.array_len.get(&base_addr.as_u64()) {
                                let len = byte_len / size.bytes() as u64;
                                let maybe_set = S::maybe_set(|| {
                                    (0..len).map(|i| {
                                        cx.a(explorer
                                            .platform
                                            .rom()
                                            .load(
                                                mem_type,
                                                Const::new(base_addr.size, base_addr.as_u64() + i),
                                                size,
                                            )
                                            .unwrap())
                                            .into()
                                    })
                                });
                                if let Some(set) = maybe_set {
                                    return set;
                                }
                            } else {
                                // HACK(eddyb) try to guess when what we're assuming to
                                // be the index can't realistically be a pointer itself.
                                let index_may_be_pointer = match cx[index] {
                                    // FIXME(eddyb) actually check the parameters here.
                                    Node::Int(IntOp::Shl, ..)
                                    | Node::Int(IntOp::ShrU, ..)
                                    | Node::Zext(..) => false,

                                    _ => true,
                                };

                                if !index_may_be_pointer {
                                    if let Ok(v) =
                                        explorer.platform.rom().load(mem_type, base_addr, size)
                                    {
                                        println!(
                                            "explore: possible array indexing with base {:?}, \
                                             assuming index ({}) is 0 and ignoring other values",
                                            base_addr,
                                            cx.pretty_print(&index),
                                        );
                                        println!(
                                            "    help: you can indicate the array address range \
                                             with e.g. `-a {:?}..{:?}` for a length of 1",
                                            base_addr,
                                            Const::new(
                                                base_addr.size,
                                                base_addr.as_u64() + size.bytes() as u64
                                            ),
                                        );
                                        return cx.a(v).into();
                                    }
                                }
                            }
                        }
                    }
                }

                cx.a(Node::Load(MemRef {
                    mem: self,
                    mem_type: cx[self].ty(cx).mem().unwrap(),
                    addr,
                    size,
                }))
                .into()
            }

            Node::Store(r, v) => r.addr.subst_reduce::<S>(explorer, base).flat_map(|r_addr| {
                if r_addr == addr && r.size == size {
                    v.subst_reduce(explorer, base)
                } else {
                    r.mem.subst_reduce_load(explorer, base, addr, size)
                }
            }),

            _ => unreachable!(),
        }
    }

    // FIXME(eddyb) introduce a more general "folder" abstraction.
    fn subst_reduce<S: MaybeSet<INode>>(self, explorer: &Explorer<'_>, base: Option<&State>) -> S {
        let subst_reduce = |x: INode| x.subst_reduce::<S>(explorer, base);
        let cx = explorer.cx;
        match cx[self] {
            Node::GlobalIn(g) => base
                .and_then(|base| base.globals.get(&g).copied())
                .map_or(self.into(), |node| node.subst_reduce(explorer, None)),

            Node::Const(_) => self.into(),

            Node::Int(op, size, a, b) => subst_reduce(a)
                .flat_map(|a| subst_reduce(b).flat_map(|b| cx.a(Node::Int(op, size, a, b)).into())),
            Node::Trunc(size, x) => subst_reduce(x).flat_map(|x| cx.a(Node::Trunc(size, x)).into()),
            Node::Sext(size, x) => subst_reduce(x).flat_map(|x| cx.a(Node::Sext(size, x)).into()),
            Node::Zext(size, x) => subst_reduce(x).flat_map(|x| cx.a(Node::Zext(size, x)).into()),
            Node::Load(r) => subst_reduce(r.addr)
                .flat_map(|addr| r.mem.subst_reduce_load(explorer, base, addr, r.size)),

            Node::Store(r, x) => subst_reduce(r.mem).flat_map(|mem| {
                subst_reduce(r.addr).flat_map(|addr| {
                    subst_reduce(x).flat_map(|x| {
                        cx.a(Node::Store(
                            MemRef {
                                mem,
                                mem_type: r.mem_type,
                                addr,
                                size: r.size,
                            },
                            x,
                        ))
                        .into()
                    })
                })
            }),
        }
    }
}

/// Options for handling an exit "continuation".
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct ExitOptions {
    /// Argument values for the exit "continuation".
    /// These will be back-propagated through jumps, to the exit "continuation".
    // FIXME(eddyb) `SmallVec` doesn't seem to be faster than `Vec`?!
    args_values: SmallVec<[INode; 4]>,
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

    /// One set of values per "continuation argument".
    /// Must be the same length as the `args_values` in `ExitOptions`.
    // TODO(eddyb) should this be per `targets` value?
    // FIXME(eddyb) `SmallVec` doesn't seem to be faster than `Vec`?!
    args_values: SmallVec<[Set1<INode>; 4]>,

    /// Indicates whether this (sub-)CFG contains unresolved
    /// cycles, which may have resulted in the computed exit
    /// being different from the eventual fixpoint.
    partial: Option<Partial>,
}

impl Exit {
    fn merge(self, cx: &Cx, bb: BlockId, other: Self) -> Self {
        if let (Set1::One(a), Set1::One(b)) = (self.targets, other.targets) {
            if a != b {
                println!(
                    "explore: {:?}: ambiguous targets: {} vs {}",
                    bb,
                    cx.pretty_print(&a),
                    cx.pretty_print(&b)
                );
            }
        }
        Exit {
            targets: self.targets.union(other.targets),
            args_values: self
                .args_values
                .into_iter()
                .zip_eq(other.args_values)
                .map(|(a, b)| a.union(b))
                .collect(),
            partial: self.partial.or(other.partial),
        }
    }
}

pub struct Explorer<'a> {
    pub cx: &'a Cx,
    pub platform: &'a dyn Platform,
    pub blocks: BTreeMap<BlockId, Block>,

    /// Analysis input indicating the length of an array, in bytes.
    pub array_len: HashMap<u64, u64>,

    /// Analysis output indicating that a block takes a "continuation" which is
    /// static in some ancestors, e.g. callees taking the return "continuation".
    /// The values are the ancestors (see also `eventual_static_continuation`).
    pub takes_static_continuation: HashMap<BlockId, BTreeSet<BlockId>>,

    /// Analysis output indicating that a block will eventually reach another
    /// block by going through some sub-CFG that takes a "continuation",
    /// e.g. calls reaching the return "continuation".
    pub eventual_static_continuation: HashMap<BlockId, BlockId>,

    cancel_token: Option<&'a AtomicBool>,

    status_term: Option<Box<term::StderrTerminal>>,

    exit_cache: HashMap<(BlockId, ExitOptions), Exit>,
}

impl Drop for Explorer<'_> {
    fn drop(&mut self) {
        if let Some(term) = &mut self.status_term {
            let _ = term.reset();
            let _ = writeln!(term.get_mut(), "");
            let _ = term.get_mut().flush();
        }
    }
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
            array_len: HashMap::new(),
            takes_static_continuation: HashMap::new(),
            eventual_static_continuation: HashMap::new(),
            cancel_token,
            status_term: term::stderr(),
            exit_cache: HashMap::new(),
        }
    }

    pub fn get_or_lift_block(&mut self, bb: BlockId) -> &Block {
        // FIXME(eddyb) clean this up whenever NLL/Polonius can do the
        // efficient check (`if let Some(x) = map.get(k) { return x; }`).
        while !self.blocks.contains_key(&bb) {
            let mut state = State::default();
            let mut pc = Const::new(
                self.cx[self.platform.isa().mem_containing_rom()]
                    .ty
                    .mem()
                    .unwrap()
                    .addr_size,
                bb.entry_pc,
            );
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

            if let Some(term) = &mut self.status_term {
                if term.carriage_return().is_ok() && term.delete_line().is_ok() {
                    let _ = write!(
                        term.get_mut(),
                        "Last lifted block: {:?} | Total found blocks: {}",
                        bb,
                        self.blocks.len()
                    );
                    let _ = term.get_mut().flush();
                }
            }

            break;
        }

        &self.blocks[&bb]
    }

    fn get_block_targets(&self, bb: BlockId) -> Edges<SmallSet<INode>> {
        self.blocks[&bb].edges.as_ref().map(|e, _| match e.effect {
            Effect::Jump(target)
            | Effect::Opaque {
                next_pc: target, ..
            } => target.subst_reduce::<SmallSet<_>>(self, None),
            Effect::Error(_) => SmallSet::Empty,
        })
    }

    /// Get the constant jump targets of a block, as seen by the analysis.
    // HACK(eddyb) this shouldn't be needed, but jump table support
    // (via `-a`/`--array`) isn't baked into the `Block`s themselves.
    pub fn get_block_direct_targets(&self, bb: BlockId) -> Edges<SmallSet<BlockId>> {
        self.get_block_targets(bb).map(|targets, _| {
            let mut direct_targets = SmallSet::Empty;
            for target in targets.into_iter() {
                if let Some(target_bb) = self.cx[target].as_const().map(BlockId::from) {
                    direct_targets.insert(target_bb);
                }
            }
            direct_targets
        })
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

        let exit = self.find_exit(entry_bb, &ExitOptions::default());
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
        options: &ExitOptions,
        br_cond: Option<bool>,
        direct_target: INode,
    ) -> Exit {
        let mut exit =
            Exit {
                targets: Set1::One(direct_target),

                // FIXME(eddyb) compute this lazily? (it may not be used)
                args_values: options
                    .args_values
                    .iter()
                    .map(|&arg_value| {
                        Set1::One(arg_value.subst_reduce(
                            self,
                            Some(&self.blocks[&bb].edges.as_ref()[br_cond].state),
                        ))
                    })
                    .collect(),

                partial: None,
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
                let all_args_values_are_const =
                    exit.args_values.iter().all(|&arg_values| match arg_values {
                        Set1::Empty | Set1::Many => true,
                        Set1::One(value) => self.cx[value].as_const().is_some(),
                    });
                if all_args_values_are_const {
                    exit.targets = Set1::Empty;
                    return exit;
                }
            }

            if let [prev_target_bb] = stack[..] {
                self.takes_static_continuation
                    .entry(prev_target_bb)
                    .or_default()
                    .insert(bb);
                // HACK(eddyb) save the observed value without accounting
                // for multiple possible values etc.
                self.eventual_static_continuation.insert(bb, target_bb);
            }

            // Recurse on the current target.
            let target_exit = self.find_exit(target_bb, options);
            // FIXME(eddyb) abstract composing `partial`s better.
            exit.partial = exit.partial.or(target_exit.partial);
            let mut resolve_values = |all_values: &mut SmallVec<[Set1<INode>; 4]>| {
                // FIXME(eddyb) disabled because of potential overhead, must
                // measure before turning it back on! (especially as it's doing
                // some really inefficient searches... should build a map!)
                if false {
                    // Reuse the already computed `args_values` where possible.
                    let all_const_or_in_args_values =
                        all_values.iter().all(|&values| match values {
                            Set1::Empty | Set1::Many => true,
                            Set1::One(v) => {
                                self.cx[v].as_const().is_some() || options.args_values.contains(&v)
                            }
                        });
                    if all_const_or_in_args_values {
                        for values in all_values {
                            *values = (*values).flat_map(|value| {
                                exit.args_values[options
                                    .args_values
                                    .iter()
                                    .position(|&a| a == value)
                                    .unwrap()]
                            });
                        }
                        return;
                    }
                }

                for &frame_bb in stack.iter().rev() {
                    // Common closure to avoid mismatching when filtering down
                    // all the `Set1<INode>` to just the `INode`s, to resolve.
                    let resolvable_all_values_slot = |&slot: &Set1<INode>| match slot {
                        Set1::Empty | Set1::Many => None,
                        Set1::One(v) => {
                            // Constants don't need any propagation work.
                            if self.cx[v].as_const().is_some() {
                                return None;
                            }

                            Some(v)
                        }
                    };
                    let resolvable_values: SmallVec<[INode; 4]> = all_values
                        .iter()
                        .filter_map(resolvable_all_values_slot)
                        .collect();
                    let resolvable_values_mut = all_values
                        .iter_mut()
                        .filter(|slot| resolvable_all_values_slot(slot).is_some());
                    if !resolvable_values.is_empty() {
                        let frame_exit = self.find_exit(
                            frame_bb,
                            &ExitOptions {
                                args_values: resolvable_values,
                            },
                        );
                        exit.partial = exit.partial.take().or(frame_exit.partial);

                        for (slot, frame_resolved) in
                            resolvable_values_mut.zip_eq(frame_exit.args_values)
                        {
                            *slot = frame_resolved;
                        }
                    }
                }
                for values in all_values {
                    *values = values.map(|value| {
                        value.subst_reduce(
                            self,
                            Some(&self.blocks[&bb].edges.as_ref()[br_cond].state),
                        )
                    });
                }
            };

            let mut args_values_and_targets = target_exit
                .args_values
                .iter()
                .copied()
                .chain([target_exit.targets])
                .collect();
            resolve_values(&mut args_values_and_targets);

            let targets = args_values_and_targets.pop().unwrap();
            let args_values = args_values_and_targets;

            exit.targets = targets;
            exit.args_values = args_values;

            stack.push(target_bb);
        }
    }

    fn find_exit_uncached(&mut self, bb: BlockId, options: &ExitOptions) -> Exit {
        let cx = self.cx;
        self.get_or_lift_block(bb);

        // TODO(eddyb) avoid duplicating work between all the possible targets,
        // inside `exit_from_target`, when they converge early.
        let edge_targets = self.get_block_targets(bb);

        // HACK(eddyb) work around `get_or_lift_block` not splitting existing
        // blocks, and there being no mechanism to avoid overlapping blocks,
        // by eagerly lifting the branch target that has a higher address.
        if let Edges::Branch { .. } = edge_targets {
            edge_targets
                .as_ref()
                .map(|targets, _| match targets {
                    SmallSet::One(target) => self.cx[*target].as_const().map(BlockId::from),
                    _ => None,
                })
                .merge(|t, e| Some(t?.max(e?)))
                .map(|max_target_bb| self.get_or_lift_block(max_target_bb));
        }

        edge_targets
            .map(|targets, br_cond| {
                targets
                    .into_iter()
                    .map(|target| self.find_exit_uncached_on_edge(bb, options, br_cond, target))
                    .fold(
                        Exit {
                            targets: Set1::Empty,
                            // FIXME(eddyb) avoid preallocating here somehow.
                            args_values: iter::repeat(Set1::Empty)
                                .take(options.args_values.len())
                                .collect(),
                            partial: None,
                        },
                        |a, b| a.merge(cx, bb, b),
                    )
            })
            .merge(|t, e| t.merge(cx, bb, e))
    }

    // FIXME(eddyb) reuse cached value when it doesn't interact with `options`.
    fn find_exit(&mut self, bb: BlockId, options: &ExitOptions) -> Exit {
        // FIXME(eddyb) avoid cloning here, perhaps by allocating `ExitOptions`
        // in an `elsa::FrozenVec`, since it's kept alive by the cache anyway.
        match self.exit_cache.entry((bb, options.clone())) {
            Entry::Occupied(mut entry) => {
                let cached = entry.get_mut();
                return Exit {
                    targets: cached.targets,
                    // FIXME(eddyb) avoid cloning here (keep it in an `Rc`?).
                    args_values: cached.args_values.clone(),
                    partial: cached.partial.as_mut().map(|partial| {
                        partial.observed = true;
                        Partial { observed: false }
                    }),
                };
            }
            Entry::Vacant(entry) => {
                entry.insert(Exit {
                    targets: Set1::Empty,
                    // FIXME(eddyb) avoid preallocating here somehow.
                    args_values: iter::repeat(Set1::Empty)
                        .take(options.args_values.len())
                        .collect(),
                    partial: Some(Partial { observed: false }),
                });
            }
        }

        // TODO(eddyb) actually show that retrying `find_exit_uncached`
        // has *any* effect on the overall results!
        // It *might* be the case that not caching a partial value
        // (i.e. the `entry.remove()` call) has a similar effect?
        loop {
            let mut exit = self.find_exit_uncached(bb, &options);

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

            // FIXME(eddyb) avoid cloning here, perhaps by allocating `ExitOptions`
            // in an `elsa::FrozenVec`, since it's kept alive by the cache anyway.
            let mut entry = match self.exit_cache.entry((bb, options.clone())) {
                Entry::Occupied(entry) => entry,
                Entry::Vacant(_) => unreachable!(),
            };
            let cached = entry.get_mut();
            let old_targets = mem::replace(&mut cached.targets, exit.targets);
            // FIXME(eddyb) avoid cloning here (keep it in an `Rc`?).
            let old_args_values = mem::replace(&mut cached.args_values, exit.args_values.clone());
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
            let progress = progress(old_targets, exit.targets)
                | old_args_values
                    .iter()
                    .zip_eq(&exit.args_values)
                    .any(|(&old, &new)| progress(old, new));
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

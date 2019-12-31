use crate::explore::{BlockId, Explorer};
use crate::ir::{Edges, Effect, Val, Visit, Visitor};
use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::iter;
use std::mem;

struct NestedBlock {
    per_edge_child: [Option<BlockId>; 2],
    children: Vec<BlockId>,
    forward_exits: BTreeMap<BlockId, usize>,
}

pub struct Nester<'a, P> {
    pub explorer: &'a Explorer<'a, P>,
    ref_counts: HashMap<BlockId, usize>,

    nested_block_cache: HashMap<BlockId, NestedBlock>,
}

impl<'a, P> Nester<'a, P> {
    pub fn new(explorer: &'a Explorer<'a, P>) -> Self {
        let mut nester = Nester {
            explorer,
            ref_counts: HashMap::new(),
            nested_block_cache: HashMap::new(),
        };

        let mut seen = HashMap::new();
        for &bb in explorer.blocks.keys() {
            nester.compute_ref_counts(bb, &mut seen);
        }

        nester
    }

    /// Gather all the ref counts in the sub-CFG statically reachable from `bb`,
    /// taking care not to count backedges, as they would always prevent nesting
    /// the loops they're in, for no good reason.
    fn compute_ref_counts(&mut self, bb: BlockId, seen: &mut HashMap<BlockId, bool>) {
        // Avoid counting any block's targets more than once.
        match seen.entry(bb) {
            Entry::Occupied(_) => return,
            Entry::Vacant(entry) => {
                // HACK(eddyb) use `seen[bb] == false` as an indicator that `bb`
                // is an ancestor in the CFG being reached from it.
                entry.insert(false);
            }
        }

        let explorer = self.explorer;
        let block = &explorer.blocks[&bb];

        let mut add_target = |target| {
            // Ignore loop backedges, using `seen[target] == false` as an
            // indicator that `target` is an ancestor in the CFG.
            if seen.get(&target) != Some(&false) {
                *self.ref_counts.entry(target).or_default() += 1;
                self.compute_ref_counts(target, seen);
            }
        };
        block.edges.as_ref().map(|e, _| match e.effect {
            Effect::Jump(target)
            | Effect::Opaque {
                next_pc: target, ..
            } => {
                if let Some(target) = explorer.cx[target].as_const().map(BlockId::from) {
                    add_target(target);
                }
            }
            Effect::Error(_) => {}
        });
        if let Some(&target_bb) = explorer.eventual_static_continuation.get(&bb) {
            add_target(target_bb);
        }

        seen.insert(bb, true);
    }

    pub fn root_nested_blocks(&mut self) -> Vec<BlockId> {
        let mut root_blocks = vec![];

        let cx = self.explorer.cx;
        let mut blocks = self
            .explorer
            .blocks
            .iter()
            .map(|(&bb, block)| {
                (
                    bb,
                    block.edges.as_ref().map(|e, _| match e.effect {
                        Effect::Jump(target)
                        | Effect::Opaque {
                            next_pc: target, ..
                        } => cx[target].as_const().map(BlockId::from),
                        Effect::Error(_) => None,
                    }),
                )
            })
            .peekable();

        while let Some(&(bb, _)) = blocks.peek() {
            self.compute_nested_block(&mut blocks);
            root_blocks.push(bb);
        }

        root_blocks
    }

    fn compute_nested_block(
        &mut self,
        blocks: &mut iter::Peekable<impl Iterator<Item = (BlockId, Edges<Option<BlockId>>)>>,
    ) {
        let (bb, edge_targets) = blocks.next().unwrap();
        assert!(!self.nested_block_cache.contains_key(&bb));

        let edge_targets = match edge_targets {
            Edges::One(target) => [target.map(|x| (x, None)), None],
            Edges::Branch { cond: _, t, e } => {
                let t = t.map(|x| (x, Some(true)));
                let e = e.map(|x| (x, Some(false)));
                if t < e {
                    [t, e]
                } else {
                    [e, t]
                }
            }
        };

        let mut children = vec![];
        let mut per_edge_child = [None, None];
        let mut forward_exits = BTreeMap::new();

        for (target, br_cond) in edge_targets.iter().copied().flatten() {
            // Don't nest backwards jumps, or jumps that look like functions.
            if target <= bb || self.explorer.takes_static_continuation.contains(&target) {
                continue;
            }

            if blocks.peek().map(|&(bb, _)| bb) != Some(target) || self.ref_counts[&target] > 1 {
                *forward_exits.entry(target).or_default() += 1;
                continue;
            }

            self.compute_nested_block(blocks);
            let child = &self.nested_block_cache[&target];
            for (&child_exit, &count) in &child.forward_exits {
                *forward_exits.entry(child_exit).or_default() += count;
            }
            match br_cond {
                Some(i) => {
                    assert!(per_edge_child[i as usize].replace(target).is_none());
                }
                None => children.push(target),
            }
        }

        // Include any targets that could be the return from a call.
        if let Some(&target_bb) = self.explorer.eventual_static_continuation.get(&bb) {
            if target_bb > bb {
                *forward_exits.entry(target_bb).or_default() += 1;
            }
        }

        // Also collect any merges (combined refcounts match total) as children.
        while let Some(&(next_bb, _)) = blocks.peek() {
            let count = match forward_exits.get(&next_bb) {
                Some(&x) => x,
                None => break,
            };
            if count < self.ref_counts.get(&next_bb).copied().unwrap_or(0) {
                break;
            }

            // Don't nest exit targets that look like functions.
            if self.explorer.takes_static_continuation.contains(&next_bb) {
                break;
            }

            forward_exits.remove(&next_bb);

            self.compute_nested_block(blocks);
            let child = &self.nested_block_cache[&next_bb];
            for (&child_exit, &count) in &child.forward_exits {
                *forward_exits.entry(child_exit).or_default() += count;
            }
            children.push(next_bb);
        }

        self.nested_block_cache.insert(
            bb,
            NestedBlock {
                per_edge_child,
                children,
                forward_exits,
            },
        );
    }

    // FIXME(eddyb) do this without allocating temporary `String`s.
    pub fn nested_block_to_string(&self, bb: BlockId) -> String {
        struct WithSuffix<T>(T, String);

        impl<T: Visit> Visit for WithSuffix<T> {
            fn walk(&self, visitor: &mut impl Visitor) {
                self.0.visit(visitor);
            }
        }

        impl<T: fmt::Debug> fmt::Debug for WithSuffix<T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.fmt(f)?;
                f.write_str(&self.1)
            }
        }

        let nested_block = &self.nested_block_cache[&bb];

        // HACK(eddyb) sort branch edges if both have children.
        let mut edges = self.explorer.blocks[&bb].edges.as_ref();
        let mut per_edge_child = [
            nested_block.per_edge_child[0],
            nested_block.per_edge_child[1],
        ];
        if let [Some(e_child), Some(t_child)] = &mut per_edge_child {
            if t_child > e_child {
                if let Edges::Branch { cond, t, e } = &mut edges {
                    mem::swap(t_child, e_child);
                    mem::swap(t, e);
                    *cond = self.explorer.cx.a(Val::bit_not(*cond));
                }
            }
        }

        let edges = edges.map(|e, br_cond| {
            let suffix =
                br_cond
                    .and_then(|i| per_edge_child[i as usize])
                    .map_or(String::new(), |child| {
                        format!(
                            "\n        {}",
                            self.nested_block_to_string(child)
                                .replace("\n", "\n        ")
                        )
                    });
            (&e.state, WithSuffix(&e.effect, suffix))
        });

        let mut body = self
            .explorer
            .cx
            .pretty_print_with_states_on_edges(edges.as_ref().map(|e, _| (e.0, &e.1)))
            .to_string();

        if !nested_block.children.is_empty() {
            // HACK(eddyb) "re-open" the outermost `{...}`, or create it if missing.
            if body.starts_with("{\n") && body.ends_with("\n}") {
                body.pop();
            } else {
                body.insert_str(0, "{\n    ");
                body += "\n";
            }

            for &child in &nested_block.children {
                body += "    ";
                body += &self.nested_block_to_string(child).replace("\n", "\n    ");
                body += "\n";
            }

            // Close the outermost `{...}` back up.
            body += "}";
        }

        // FIXME(eddyb) this is wasteful, avoid copying the string around like that.
        format!("{:?} {}", bb, body)
    }
}

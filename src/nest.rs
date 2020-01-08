use crate::explore::{BlockId, Explorer};
use crate::ir::{Const, Edges, Node, Visit, Visitor};
use elsa::FrozenMap;
use itertools::{Either, Itertools};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::{self, Write};
use std::mem;
use std::ops::RangeTo;

struct NestedBlock {
    pc: RangeTo<Const>,

    per_edge_child: [Option<BlockId>; 2],
    children: Vec<BlockId>,
    static_exits: BTreeMap<BlockId, usize>,
}

pub struct Nester<'a> {
    pub explorer: &'a Explorer<'a>,
    ref_counts: HashMap<BlockId, usize>,
    function_like: HashSet<BlockId>,

    nested_block_cache: FrozenMap<BlockId, Box<NestedBlock>>,
}

impl<'a> Nester<'a> {
    pub fn new(explorer: &'a Explorer<'a>) -> Self {
        // HACK(eddyb) only consider blocks to be function entry points if the
        // presumed return continuation immediatelly follows the caller block.
        let function_like = explorer
            .takes_static_continuation
            .iter()
            .filter(|&(&_, callers)| {
                callers.iter().any(|caller_bb| {
                    explorer
                        .eventual_static_continuation
                        .get(&caller_bb)
                        .map_or(false, |&ret_bb| {
                            ret_bb == BlockId::from(explorer.blocks[&caller_bb].pc.end)
                        })
                })
            })
            .map(|(&callee_bb, _)| callee_bb)
            .collect();

        let mut nester = Nester {
            explorer,
            ref_counts: HashMap::new(),
            function_like,
            nested_block_cache: FrozenMap::new(),
        };

        let mut refcount_target = |target| {
            *nester.ref_counts.entry(target).or_default() += 1;
        };
        for &bb in explorer.blocks.keys() {
            explorer.get_block_direct_targets(bb).map(|targets, _| {
                for target in targets.into_iter() {
                    refcount_target(target);
                }
            });

            if let Some(&target_bb) = explorer.eventual_static_continuation.get(&bb) {
                refcount_target(target_bb);
            }
        }

        nester
    }

    fn get_or_compute_nested_block(&self, bb: BlockId) -> &NestedBlock {
        if let Some(nested_block) = self.nested_block_cache.get(&bb) {
            return nested_block;
        }

        let block = &self.explorer.blocks[&bb];

        let edge_targets = self
            .explorer
            .get_block_direct_targets(bb)
            .map(|targets, br_cond| targets.into_iter().map(move |target| (target, br_cond)));
        let edge_targets = match edge_targets {
            Edges::One(targets) => Either::Left(targets),
            Edges::Branch { t, e, .. } => Either::Right(t.merge(e)),
        };

        let mut pc = block.pc;
        let mut children = vec![];
        let mut per_edge_child = [None, None];
        let mut static_exits = BTreeMap::new();

        for (target, br_cond) in edge_targets {
            // Don't nest jumps to targets that look like functions, and don't
            // even include them in `static_exits`.
            if self.function_like.contains(&target) {
                continue;
            }

            let next_bb = self
                .explorer
                .blocks
                .range(BlockId::from(pc.end)..)
                .map(|(&bb, _)| bb)
                .next();

            if next_bb != Some(target) || self.ref_counts[&target] > 1 {
                *static_exits.entry(target).or_default() += 1;
                continue;
            }

            let child = self.get_or_compute_nested_block(target);
            pc.end = child.pc.end;
            for (&child_exit, &count) in &child.static_exits {
                *static_exits.entry(child_exit).or_default() += count;
            }

            if let Some(i) = br_cond {
                if per_edge_child[i as usize].is_none() {
                    per_edge_child[i as usize] = Some(target);
                    continue;
                }
            }

            children.push(target);
        }

        // Include any targets that could be the return from a call.
        if let Some(&target_bb) = self.explorer.eventual_static_continuation.get(&bb) {
            if target_bb > bb {
                *static_exits.entry(target_bb).or_default() += 1;
            }
        }

        // Also collect any merges (combined refcounts match total) as children.
        // This is done in two steps to allow non-loop jumps backwards within
        // a function (e.g. backwards goto, odd codegen, or handwritten asm).

        // Step 1: collect as many merges as possible, ignoring refcounts,
        // but accumulating a best-case version of `static_exits`.
        let mut merge_pc = pc;
        let mut merge_static_exits = static_exits.clone();
        let mut merge_children = vec![];
        while let Some((&next_bb, _)) = self
            .explorer
            .blocks
            .range(BlockId::from(merge_pc.end)..)
            .next()
        {
            // Only stop if we're past the last reachable block.
            // This allows some blocks to only be reached through later blocks
            // (this is properly checked in the second step).
            // FIXME(eddyb) perhaps optimize this?
            if merge_static_exits.range(next_bb..).next().is_none() {
                break;
            }

            // Don't nest exit targets that look like functions.
            if self.function_like.contains(&next_bb) {
                break;
            }

            let child = self.get_or_compute_nested_block(next_bb);
            if merge_pc.end == child.pc.end {
                // HACK(eddyb) avoid infinite loops with 0-length children.
                break;
            }
            merge_pc.end = child.pc.end;
            for (&child_exit, &count) in &child.static_exits {
                *merge_static_exits.entry(child_exit).or_default() += count;
            }
            merge_children.push((next_bb, child));
        }

        // Step 2: truncate `merge_children`, based on `merge_static_exits`
        // matching the refcount, and recompute `merge_static_exits` using the
        // truncated list. Keep repeating until `merge_children` stops changing.
        loop {
            let old_merge_children_count = merge_children.len();
            let valid_merge_children = merge_children
                .iter()
                .take_while(|&(child_bb, _)| match merge_static_exits.get(&child_bb) {
                    Some(&count) => count >= self.ref_counts.get(&child_bb).copied().unwrap_or(0),
                    None => false,
                })
                .count();
            merge_children.truncate(valid_merge_children);

            if old_merge_children_count == merge_children.len() {
                break;
            }

            // FIXME(eddyb) perhaps make this less expensive?
            merge_static_exits = static_exits.clone();
            for (_, child) in &merge_children {
                for (&child_exit, &count) in &child.static_exits {
                    *merge_static_exits.entry(child_exit).or_default() += count;
                }
            }
        }

        // Combine the above merge children into this nested block.
        if let Some((_, child)) = merge_children.last() {
            pc.end = child.pc.end;
        }
        children.extend(merge_children.into_iter().map(|(child_bb, _)| child_bb));
        static_exits = merge_static_exits;

        // Don't include any `children` in `static_exits`.
        for &child_bb in &children {
            static_exits.remove(&child_bb);
        }

        self.nested_block_cache.insert(
            bb,
            Box::new(NestedBlock {
                pc,
                per_edge_child,
                children,
                static_exits,
            }),
        )
    }

    // FIXME(eddyb) do this without allocating temporary `String`s.
    pub fn nested_block_to_string(&self, bb: BlockId, parent_pc: &mut RangeTo<Const>) -> String {
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

        let nested_block = self.get_or_compute_nested_block(bb);
        let block = &self.explorer.blocks[&bb];

        // HACK(eddyb) sort branch edges if both have children.
        let mut edges = block.edges.as_ref();
        let mut per_edge_child = [
            nested_block.per_edge_child[0],
            nested_block.per_edge_child[1],
        ];
        if let [Some(e_child), Some(t_child)] = &mut per_edge_child {
            if t_child > e_child {
                if let Edges::Branch { cond, t, e } = &mut edges {
                    mem::swap(t_child, e_child);
                    mem::swap(t, e);
                    *cond = self.explorer.cx.a(Node::bit_not(*cond));
                }
            }
        }

        let mut pc = block.pc;

        let edges = edges.map(|e, br_cond| {
            let suffix =
                br_cond
                    .and_then(|i| per_edge_child[i as usize])
                    .map_or(String::new(), |child| {
                        format!(
                            "\n        {}",
                            self.nested_block_to_string(child, &mut pc)
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
                body += &self
                    .nested_block_to_string(child, &mut pc)
                    .replace("\n", "\n    ");
                body += "\n";
            }

            // Close the outermost `{...}` back up.
            body += "}";
        }

        let mut s = String::new();

        if parent_pc.end.as_u64() < bb.entry_pc {
            let _ = writeln!(s, "{:?} {{", parent_pc.end);
            let _ = writeln!(
                s,
                "    /* {} unanalyzed bytes */",
                bb.entry_pc - parent_pc.end.as_u64()
            );
            let _ = writeln!(s, "}}");
        }
        parent_pc.end = nested_block.pc.end;

        // FIXME(eddyb) this is wasteful, avoid copying the string around like that.
        let _ = write!(s, "{:?} {}", bb, body);

        s
    }
}

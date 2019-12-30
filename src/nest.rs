use crate::explore::{BlockId, Explorer};
use crate::ir::{Edges, Effect, Val, Visit, Visitor};
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::iter;
use std::mem;

pub struct NestedBlock {
    bb: BlockId,
    per_edge_child: [Option<Box<NestedBlock>>; 2],
    children: Vec<NestedBlock>,
    forward_exits: BTreeMap<BlockId, usize>,
}

pub struct Nester<'a, P> {
    pub explorer: &'a Explorer<'a, P>,
    ref_counts: HashMap<BlockId, usize>,
}

impl<'a, P> Nester<'a, P> {
    pub fn new(explorer: &'a Explorer<'a, P>) -> Self {
        let cx = explorer.cx;

        let mut nester = Nester {
            explorer,
            ref_counts: HashMap::new(),
        };

        for (&bb, block) in &explorer.blocks {
            block.edges.as_ref().map(|e, _| match e.effect {
                Effect::Jump(target)
                | Effect::Opaque {
                    next_pc: target, ..
                } => {
                    if let Some(target) = cx[target].as_const().map(BlockId::from) {
                        // Ignore self-loop backedges, as they would always
                        // prevent nesting the loop for no good reason.
                        if target != bb {
                            *nester.ref_counts.entry(target).or_default() += 1;
                        }
                    }
                }
                Effect::Error(_) => {}
            });
        }

        nester
    }

    pub fn all_nested_blocks(&self) -> Vec<NestedBlock> {
        let mut nested_blocks = vec![];

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
                        } => self.explorer.cx[target].as_const().map(BlockId::from),
                        Effect::Error(_) => None,
                    }),
                )
            })
            .peekable();

        while blocks.peek().is_some() {
            nested_blocks.push(self.nested_block_from_blocks(&mut blocks));
        }

        nested_blocks
    }

    fn nested_block_from_blocks(
        &self,
        blocks: &mut iter::Peekable<impl Iterator<Item = (BlockId, Edges<Option<BlockId>>)>>,
    ) -> NestedBlock {
        let (bb, edge_targets) = blocks.next().unwrap();

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
            // Don't stop if we see a backwards jump, but also don't nest it.
            if target <= bb {
                continue;
            }

            if blocks.peek().map(|&(bb, _)| bb) != Some(target) || self.ref_counts[&target] > 1 {
                *forward_exits.entry(target).or_default() += 1;
                continue;
            }

            let child = self.nested_block_from_blocks(blocks);
            for (&child_exit, &count) in &child.forward_exits {
                *forward_exits.entry(child_exit).or_default() += count;
            }
            match br_cond {
                Some(i) => {
                    assert!(per_edge_child[i as usize]
                        .replace(Box::new(child))
                        .is_none());
                }
                None => children.push(child),
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

            forward_exits.remove(&next_bb);

            let child = self.nested_block_from_blocks(blocks);
            for (&child_exit, &count) in &child.forward_exits {
                *forward_exits.entry(child_exit).or_default() += count;
            }
            children.push(child);
        }

        NestedBlock {
            bb,
            per_edge_child,
            children,
            forward_exits,
        }
    }

    // FIXME(eddyb) do this without allocating temporary `String`s.
    pub fn nested_block_to_string(&self, nested_block: &NestedBlock) -> String {
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

        let bb = nested_block.bb;

        // HACK(eddyb) sort branch edges if both have children.
        let mut edges = self.explorer.blocks[&bb].edges.as_ref();
        let mut per_edge_child = [
            nested_block.per_edge_child[0].as_ref(),
            nested_block.per_edge_child[1].as_ref(),
        ];
        if let [Some(e_child), Some(t_child)] = &mut per_edge_child {
            if t_child.bb > e_child.bb {
                if let Edges::Branch { cond, t, e } = &mut edges {
                    mem::swap(t_child, e_child);
                    mem::swap(t, e);
                    *cond = self.explorer.cx.a(Val::bit_not(*cond));
                }
            }
        }

        let edges = edges.map(|e, br_cond| {
            let suffix = br_cond
                .and_then(|i| per_edge_child[i as usize].as_ref())
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

            for child in &nested_block.children {
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

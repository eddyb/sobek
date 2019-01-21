use crate::ir::{Arch, Block, Const, Cx, Effect, Platform, Use, Val};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

pub struct Explorer<'a, P> {
    pub cx: &'a mut Cx<P>,
    pub blocks: BTreeMap<Const, Block>,
    preds: HashMap<Const, BTreeSet<Const>>,

    seen_bb: HashSet<Const>,
    queue: VecDeque<(Const, Const)>,
    non_const_targets: Vec<(Const, Use<Val>)>,
}

impl<'a, P: Platform> Explorer<'a, P> {
    pub fn new(cx: &'a mut Cx<P>) -> Self {
        Explorer {
            cx,
            blocks: BTreeMap::new(),
            preds: HashMap::new(),
            seen_bb: HashSet::new(),
            queue: VecDeque::new(),
            non_const_targets: vec![],
        }
    }

    pub fn get_or_lift_block(&mut self, entry_pc: Const) -> &Block {
        // FIXME(eddyb) clean this up whenever NLL/Polonius can do the
        // efficient check (`if let Some(x) = map.get(k) { return x; }`).
        if !self.blocks.contains_key(&entry_pc) {
            let mut state = self.cx.default.clone();
            let mut pc = entry_pc;
            let effect = loop {
                match P::Arch::lift_instr(self.cx, &mut pc, &mut state) {
                    Some(effect) => break effect,
                    None => {}
                }

                // Prevent blocks from overlapping where possible.
                if self.blocks.contains_key(&pc) {
                    break Effect::Jump(self.cx.a(pc));
                }
            };

            self.blocks.insert(
                entry_pc,
                Block {
                    pc: ..pc,
                    state: ..state,
                    effect,
                },
            );
        }
        &self.blocks[&entry_pc]
    }

    pub fn explore_bbs(&mut self, entry_bb: Const) {
        if self.seen_bb.insert(entry_bb) {
            self.explore_bb(entry_bb);
        }

        loop {
            let mut changed = false;
            while let Some((source_bb, bb)) = self.queue.pop_front() {
                if self.seen_bb.insert(bb) {
                    self.explore_bb(bb);
                    changed = true;
                }
                changed |= self.preds.entry(bb).or_default().insert(source_bb);
            }
            if !changed {
                break;
            }
            for &(bb, target) in &self.non_const_targets {
                TargetSearcher {
                    cx: self.cx,
                    blocks: &self.blocks,
                    preds: &self.preds,
                    queue: &mut self.queue,

                    bb,
                    stack: vec![],
                }
                .search(bb, target);
            }
        }
    }

    fn explore_bb(&mut self, bb: Const) {
        let effect = self.get_or_lift_block(bb).effect;
        let mut enqueue = |target: Use<Val>| {
            if let Some(target) = self.cx[target].as_const() {
                self.queue.push_back((bb, target));
            } else {
                self.non_const_targets.push((bb, target))
            }
        };
        match effect {
            Effect::Jump(target) => {
                enqueue(target);
            }
            Effect::Branch { t, e, .. } => {
                enqueue(t);
                enqueue(e);
            }
            Effect::PlatformCall { ret_pc, .. } => {
                self.queue.push_back((bb, ret_pc));
            }
            Effect::Trap { .. } => {}
        }
    }
}

struct TargetSearcher<'a, P> {
    cx: &'a mut Cx<P>,
    blocks: &'a BTreeMap<Const, Block>,
    preds: &'a HashMap<Const, BTreeSet<Const>>,

    queue: &'a mut VecDeque<(Const, Const)>,

    bb: Const,
    stack: Vec<Const>,
}

impl<P> TargetSearcher<'_, P> {
    fn search(&mut self, cur_bb: Const, target: Use<Val>) {
        if let Some(target) = self.cx[target].as_const() {
            self.queue.push_back((self.bb, target));
            return;
        }

        // HACK(eddyb) avoid deep backtracking.
        if self.stack.len() > 16 {
            return;
        }

        if self.stack.contains(&cur_bb) {
            return;
        }

        self.stack.push(cur_bb);

        if let Some(preds) = self.preds.get(&cur_bb) {
            for &pred in preds {
                let mut target = target.subst(self.cx, &self.blocks[&pred].state.end);

                // HACK(eddyb) try to get the last stored value.
                while let Val::Load(r) = self.cx[target] {
                    match self.cx[r.mem].guess_load(self.cx, r.addr, r.size) {
                        Some(v) => target = v,
                        None => break,
                    }
                }

                self.search(pred, target);
            }
        } else {
            println!(
                "explore: {:?} jumps to unknown {}",
                self.bb,
                self.cx.pretty_print(&self.cx[target], None)
            );
        }

        self.stack.pop();
    }
}

use crate::ir::{
    Arch, Const, Cx, Effect, IntOp, Mem, MemRef, MemSize, Platform, Reg, Rom, State, Use, Val,
};
use std::iter;

pub struct Mips32;

impl State {
    fn set(&mut self, r: usize, v: Use<Val>) {
        if r != 0 {
            self.regs[r] = v;
        }
    }
}

impl Arch for Mips32 {
    fn default_regs(cx: &mut Cx<impl Platform<Arch = Self>>) -> Vec<Use<Val>> {
        iter::once(Val::Const(Const(0)))
            .chain((1..32).map(|i| {
                Val::InReg(Reg {
                    index: i,
                    name: None,
                })
            }))
            .chain(["lo", "hi"].iter().enumerate().map(|(i, name)| {
                Val::InReg(Reg {
                    index: 32 + i,
                    name: Some(name),
                })
            }))
            .map(|v| cx.a(v))
            .collect()
    }

    fn lift_instr(
        cx: &mut Cx<impl Platform<Arch = Self>>,
        pc: &mut Const,
        state: &mut State,
    ) -> Option<Effect> {
        let instr = cx.platform.rom().load(*pc, MemSize::M32).unwrap().0;
        pc.0 += 4;

        let field = |i, w| (instr >> i) & ((1u32 << w) - 1u32);

        let op = instr >> 26;
        let (rs, rt, rd) = {
            let r = |i| field(11 + 5 * i, 5) as usize;
            (r(2), r(1), r(0))
        };
        let imm = Const(instr as i16 as i32 as u32);
        // FIXME(eddyb) ensure more aggressively that this is always 0.
        let zero = state.regs[0];

        // HACK(eddyb) work around `cx.a(Val::Foo(cx.a(Val::Bar)))` not working.
        macro_rules! val {
            ($name:ident($($arg:expr),*)) => {{
                let x = Val::$name($($arg),*);
                cx.a(x)
            }}
        }
        macro_rules! mem {
            ($name:ident($($arg:expr),*)) => {{
                let x = Mem::$name($($arg),*);
                cx.a(x)
            }}
        }

        macro_rules! link {
            ($r:expr) => {
                state.set($r, cx.a(Const(pc.0 + 4)))
            };
            () => {
                link!(31)
            };
        }
        macro_rules! jump {
            ($target:expr) => {{
                let target = $target;
                // Process delay slot.
                assert_eq!(Self::lift_instr(cx, pc, state), None);
                return Some(Effect::Jump(target));
            }};
        }
        macro_rules! branch {
            ($cond:expr => $b:expr, $t:expr, $e:expr) => {{
                let (cond, t, e) = if $b {
                    ($cond, $t, $e)
                } else {
                    ($cond, $e, $t)
                };
                // Process delay slot.
                assert_eq!(Self::lift_instr(cx, pc, state), None);
                return Some(Effect::Branch { cond, t, e });
            }};
            ($cond:expr => $b:expr) => {
                branch!($cond => $b,
                    cx.a(Const(pc.0 + 4)),
                    cx.a(Const(pc.0.wrapping_add(imm.0 << 2)))
                )
            };
        }

        if op == 0 {
            // SPECIAL (R format and syscall/break).
            let funct = field(0, 6);
            match funct {
                12 => {
                    return Some(Effect::PlatformCall {
                        code: field(6, 20),
                        ret_pc: *pc,
                    });
                }
                13 => return Some(Effect::Trap { code: field(6, 20) }),
                _ => {}
            }

            let rs = state.regs[rs];
            let rt = state.regs[rt];
            let sa = field(6, 5);
            let v = match funct {
                0 => val!(Int(IntOp::Shl, rt, cx.a(Const(sa)))),
                2 => val!(Int(IntOp::ShrU, rt, cx.a(Const(sa)))),
                3 => val!(Int(IntOp::ShrS, rt, cx.a(Const(sa)))),

                8 => jump!(rs),
                9 => {
                    link!(rd);
                    jump!(rs);
                }

                32 | 33 => val!(Int(IntOp::Add, rs, rt)),
                34 | 35 => val!(Int(IntOp::Add, rs, val!(int_neg(rt)))),
                36 => val!(Int(IntOp::And, rs, rt)),
                37 => val!(Int(IntOp::Or, rs, rt)),
                38 => val!(Int(IntOp::Xor, rs, rt)),
                39 => val!(bit_not(val!(Int(IntOp::Or, rs, rt)))),
                42 => val!(Int(IntOp::LtS, rs, rt)),
                43 => val!(Int(IntOp::LtU, rs, rt)),

                funct => {
                    eprintln!("mips: SPECIAL/funct={} unknown", funct);
                    return None;
                }
            };
            state.set(rd, v);
        } else if op == 1 {
            // REGIMM (I format w/o rt).
            let rs = state.regs[rs];
            match rt {
                0 => branch!(val!(Int(IntOp::LtS, rs, zero)) => true),
                1 => branch!(val!(Int(IntOp::LtS, rs, zero)) => false),
                _ => {
                    eprintln!("mips: REGIMM/rt={} unknown", rt);
                    return None;
                }
            }
        } else if op == 2 || op == 3 {
            // J format.
            if op == 3 {
                link!();
            }
            jump!(cx.a(Const((pc.0 & 0xc000_0000) | (field(0, 26) << 2))))
        } else {
            // I format.
            let rd = rt;
            let rs = state.regs[rs];
            let rt = state.regs[rt];

            macro_rules! mem_ref {
                ($sz:ident) => {
                    MemRef {
                        mem: state.mem,
                        addr: val!(Int(IntOp::Add, rs, cx.a(imm))),
                        size: MemSize::$sz,
                    }
                };
            }

            match op {
                4 => branch!(val!(Int(IntOp::Eq, rs, rt)) => true),
                5 => branch!(val!(Int(IntOp::Eq, rs, rt)) => false),
                6 => branch!(val!(Int(IntOp::LtS, zero, rs)) => false),
                7 => branch!(val!(Int(IntOp::LtS, zero, rs)) => true),

                8..=14 => {
                    let op = match op {
                        8 | 9 => IntOp::Add,
                        10 => IntOp::LtS,
                        11 => IntOp::LtU,
                        12 => IntOp::And,
                        13 => IntOp::Or,
                        14 => IntOp::Xor,

                        _ => unreachable!(),
                    };
                    state.set(rd, val!(Int(op, rs, cx.a(imm))));
                }
                15 => state.set(rd, cx.a(Const(imm.0 << 16))),

                35 => state.set(rd, val!(Load(mem_ref!(M32)))),
                36 => state.set(rd, val!(Load(mem_ref!(M8)))),
                37 => state.set(rd, val!(Load(mem_ref!(M16)))),

                40 => state.mem = mem!(Store(mem_ref!(M8), rt)),
                41 => state.mem = mem!(Store(mem_ref!(M16), rt)),
                43 => state.mem = mem!(Store(mem_ref!(M32), rt)),

                _ => eprintln!("mips: op={} unknown", op),
            }
        }

        None
    }
}

use crate::soft::ir::{
    BitSize::{self, *},
    Const, Cx, Edge, Edges, Effect, IntOp, Isa, Mem, MemRef, MemSize, Platform, Reg, Rom, State,
    Use, Val,
};
use std::iter;

pub struct Mips32;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    Kernel,
    Supervisor,
    User,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AddrSpace {
    Direct { cached: bool },
    Mapped(Mode),
}

impl Mips32 {
    pub fn decode_addr(addr: u32) -> (AddrSpace, u32) {
        let addr_space = match addr {
            0x0000_0000..=0x7fff_ffff => return (AddrSpace::Mapped(Mode::User), addr),

            0x8000_0000..=0x9fff_ffff => AddrSpace::Direct { cached: true },
            0xa000_0000..=0xbfff_ffff => AddrSpace::Direct { cached: false },
            0xc000_0000..=0xdfff_ffff => AddrSpace::Mapped(Mode::Supervisor),
            0xe000_0000..=0xffff_ffff => AddrSpace::Mapped(Mode::Kernel),
        };
        (addr_space, addr & 0x1fff_ffff)
    }
}

impl State {
    fn set(&mut self, r: usize, v: Use<Val>) {
        if r != 0 {
            self.regs[r] = v;
        }
    }
}

#[rustfmt::skip]
const REG_NAMES: [&str; 32] = [
    "zero",
    "at",
    "rv0", "rv1",
    "a0", "a1", "a2", "a3",
    "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7",
    "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
    "t8", "t9",
    "k0", "k1",
    "gp",
    "sp",
    "fp",
    "ra",
];

impl Isa for Mips32 {
    const ADDR_SIZE: BitSize = B32;

    fn default_regs(cx: &mut Cx<impl Platform<Isa = Self>>) -> Vec<Use<Val>> {
        iter::once(Val::Const(Const::new(B32, 0)))
            .chain((1..32).map(|i| {
                Val::InReg(Reg {
                    index: i,
                    size: B32,
                    name: REG_NAMES[i],
                })
            }))
            .chain(["lo", "hi"].iter().enumerate().map(|(i, name)| {
                Val::InReg(Reg {
                    index: 32 + i,
                    size: B32,
                    name,
                })
            }))
            .map(|v| cx.a(v))
            .collect()
    }

    fn lift_instr(
        cx: &mut Cx<impl Platform<Isa = Self>>,
        pc: &mut Const,
        mut state: State,
    ) -> Result<State, Edges<Edge>> {
        let instr = match cx.platform.rom().load(*pc, MemSize::M32) {
            Ok(x) => x.as_u32(),
            Err(e) => {
                eprintln!("mips: failed to read ROM, emitting `Trap(0)`: {:?}", e);
                return Err(Edges::One(Edge {
                    state,
                    effect: Effect::Trap { code: 0 },
                }));
            }
        };
        let add4 = |x| IntOp::Add.eval(x, Const::new(x.size, 4)).unwrap();
        *pc = add4(*pc);

        let field = |i, w| (instr >> i) & ((1u32 << w) - 1u32);

        let op = instr >> 26;
        let (rs, rt, rd) = {
            let r = |i| field(11 + 5 * i, 5) as usize;
            (r(2), r(1), r(0))
        };
        let imm = Const::new(B32, instr as i16 as i32 as u32 as u64);
        let uimm = Const::new(B32, instr as u16 as u64);
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
                state.set($r, cx.a(add4(*pc)))
            };
            () => {
                link!(31)
            };
        }
        macro_rules! jump {
            ($target:expr) => {{
                let target = $target;
                // Process delay slot.
                let delay_pc = *pc;
                state = Self::lift_instr(cx, pc, state).map_err(|edges| {
                    eprintln!(
                        "mips: delay slot at {:?} had effect, emitting `Trap(1)`: {}",
                        delay_pc,
                        cx.pretty_print_on_edges(edges.as_ref().map(|e, _| &e.effect))
                    );
                    edges.map(|e, _| Edge {
                        state: e.state,
                        effect: Effect::Trap { code: 1 },
                    })
                })?;
                return Err(Edges::One(Edge {
                    state,
                    effect: Effect::Jump(target),
                }));
            }};
        }
        macro_rules! branch_target {
            () => {
                cx.a(IntOp::Add
                    .eval(*pc, Const::new(B32, (imm.as_u32() << 2) as u64))
                    .unwrap())
            };
        }
        macro_rules! branch {
            ($cond:expr => $b:expr, $t:expr, $e:expr) => {{
                let (cond, t, e) = ($cond, $t, $e);
                let (t, e) = if $b {
                    (t, e)
                } else {
                    (e, t)
                };

                assert_eq!(cx[cond].size(), B1);

                // Process delay slot.
                let delay_pc = *pc;
                state = Self::lift_instr(cx, pc, state).map_err(|edges| {
                    eprintln!(
                        "mips: delay slot at {:?} had effect, emitting `Trap(1)`: {}",
                        delay_pc,
                        cx.pretty_print_on_edges(edges.as_ref().map(|e, _| &e.effect))
                    );
                    edges.map(|e, _| Edge {
                        state: e.state,
                        effect: Effect::Trap { code: 1 },
                    })
                })?;
                return Err(Edges::Branch {
                    cond,
                    t: Edge { state: state.clone(), effect: Effect::Jump(t) },
                    e: Edge { state: state, effect: Effect::Jump(e) },
                });
            }};
            ($cond:expr => $b:expr) => {
                branch!($cond => $b, branch_target!(), cx.a(add4(*pc)))
            };
        }

        if op == 0 {
            // SPECIAL (R format and syscall/break).
            let funct = field(0, 6);
            match funct {
                12 => {
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::PlatformCall {
                            code: field(6, 20),
                            ret_pc: cx.a(*pc),
                        },
                    }));
                }
                13 => {
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::Trap { code: field(6, 20) },
                    }))
                }
                _ => {}
            }

            let rs = state.regs[rs];
            let rt = state.regs[rt];
            let sa = field(6, 5);
            let v = match funct {
                0 => val!(Int(IntOp::Shl, B32, rt, cx.a(Const::new(B32, sa as u64)))),
                2 => val!(Int(IntOp::ShrU, B32, rt, cx.a(Const::new(B32, sa as u64)))),
                3 => val!(Int(IntOp::ShrS, B32, rt, cx.a(Const::new(B32, sa as u64)))),

                8 => jump!(rs),
                9 => {
                    link!(rd);
                    jump!(rs);
                }

                32 | 33 => val!(Int(IntOp::Add, B32, rs, rt)),
                34 | 35 => val!(int_sub(rs, rt)),
                36 => val!(Int(IntOp::And, B32, rs, rt)),
                37 => val!(Int(IntOp::Or, B32, rs, rt)),
                38 => val!(Int(IntOp::Xor, B32, rs, rt)),
                39 => val!(bit_not(val!(Int(IntOp::Or, B32, rs, rt)))),
                42 => val!(Zext(B32, val!(Int(IntOp::LtS, B32, rs, rt)))),
                43 => val!(Zext(B32, val!(Int(IntOp::LtU, B32, rs, rt)))),

                // FIXME(eddyb) figure out if these are the correct semantics for the
                // Doubleword R-format instructions in 32-bit mode on MIPS64.
                63 => val!(Trunc(
                    B32,
                    val!(Int(
                        IntOp::ShrU,
                        B64,
                        val!(Zext(B64, rt)),
                        cx.a(Const::new(B32, sa as u64 + 32))
                    ))
                )),

                funct => {
                    eprintln!(
                        "mips: SPECIAL/funct={} unknown, emitting `PlatformCall(0)`",
                        funct
                    );
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::PlatformCall {
                            code: 0,
                            ret_pc: cx.a(*pc),
                        },
                    }));
                }
            };
            state.set(rd, v);
        } else if op == 1 {
            // REGIMM (I format w/o rt).
            let rs = state.regs[rs];
            match rt {
                0 => branch!(val!(Int(IntOp::LtS, B32, rs, zero)) => true),
                1 => branch!(val!(Int(IntOp::LtS, B32, rs, zero)) => false),
                _ => {
                    eprintln!("mips: REGIMM/rt={} unknown, emitting `Trap(3)`", rt);
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::Trap { code: 3 },
                    }));
                }
            }
        } else if op == 2 || op == 3 {
            // J format.
            if op == 3 {
                link!();
            }
            jump!(cx.a(Const::new(
                B32,
                ((pc.as_u32() & 0xc000_0000) | (field(0, 26) << 2)) as u64
            )))
        } else if (op, rs, rt) == (4, 0, 0) {
            // Special-case `zero == zero` branches to jumps.
            // HACK(eddyb) this is done here to avoid const-folding
            // away control-flow in the general case.
            jump!(branch_target!());
        } else if op == 16 || op == 17 || op == 18 {
            // COPz.
            let cp = op - 16;
            let funct = field(0, 6);
            if cp == 1 {
                eprintln!(
                    "mips: COP1 (FPU), rs={}, rt={}, rd={}, funct={} unknown, ignoring",
                    rs, rt, rd, funct
                );
                return Ok(state);
            }
            eprintln!(
                "mips: COP{}, rs={}, rt={}, rd={}, funct={} unknown, emitting `PlatformCall({:?})`",
                cp,
                rs,
                rt,
                rd,
                funct,
                Const::new(B32, instr as u64),
            );
            return Err(Edges::One(Edge {
                state,
                effect: Effect::PlatformCall {
                    code: instr,
                    ret_pc: cx.a(*pc),
                },
            }));
        } else {
            // I format.
            let rd = rt;
            let rs = state.regs[rs];
            let rt = state.regs[rt];

            macro_rules! mem_ref {
                ($sz:ident) => {
                    MemRef {
                        mem: state.mem,
                        addr: val!(Int(IntOp::Add, B32, rs, cx.a(imm))),
                        size: MemSize::$sz,
                    }
                };
            }

            match op {
                4 => branch!(val!(Int(IntOp::Eq, B32, rs, rt)) => true),
                5 => branch!(val!(Int(IntOp::Eq, B32, rs, rt)) => false),
                6 => branch!(val!(Int(IntOp::LtS, B32, zero, rs)) => false),
                7 => branch!(val!(Int(IntOp::LtS, B32, zero, rs)) => true),

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
                    // HACK(eddyb) pick sign- or zero-extension based on op.
                    let imm = match op {
                        IntOp::And | IntOp::Or | IntOp::Xor => uimm,
                        _ => imm,
                    };

                    let mut v = val!(Int(op, B32, rs, cx.a(imm)));
                    if cx[v].size() == B1 {
                        v = val!(Zext(B32, v));
                    }
                    state.set(rd, v);
                }
                15 => state.set(rd, cx.a(Const::new(B32, (imm.as_u32() << 16) as u64))),

                32 => state.set(rd, val!(Sext(B32, val!(Load(mem_ref!(M8)))))),
                33 => state.set(rd, val!(Sext(B32, val!(Load(mem_ref!(M16)))))),
                35 => state.set(rd, val!(Load(mem_ref!(M32)))),
                36 => state.set(rd, val!(Zext(B32, val!(Load(mem_ref!(M8)))))),
                37 => state.set(rd, val!(Zext(B32, val!(Load(mem_ref!(M16)))))),

                40 => state.mem = mem!(Store(mem_ref!(M8), val!(Trunc(B8, rt)))),
                41 => state.mem = mem!(Store(mem_ref!(M16), val!(Trunc(B16, rt)))),
                43 => state.mem = mem!(Store(mem_ref!(M32), rt)),

                // FIXME(eddyb) figure out if these are the correct semantics for the
                // LD/SD (Load/Store Doubleword) instructions in 32-bit mode on MIPS64.
                55 => state.set(rd, val!(Trunc(B32, val!(Load(mem_ref!(M64)))))),
                63 => state.mem = mem!(Store(mem_ref!(M64), val!(Zext(B64, rt)))),

                _ => {
                    eprintln!("mips: op={} unknown, emitting `PlatformCall(1)`", op);
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::PlatformCall {
                            code: 1,
                            ret_pc: cx.a(*pc),
                        },
                    }));
                }
            }
        }

        Ok(state)
    }
}

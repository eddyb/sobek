use crate::ir::{
    BitSize::{self, *},
    Const, Cx, Edge, Edges, Effect, IntOp, Isa, Mem, MemRef, MemSize, Platform, Rom, State, Use,
    Val,
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

macro_rules! reg_names {
    ($($name:ident)*) => {
        ([$(stringify!($name)),*], [$(concat!(stringify!($name), ".upper")),*])
    }
}

const GPR_NAMES: ([&str; 32], [&str; 32]) = reg_names![
    zero
    at
    rv0 rv1
    a0 a1 a2 a3
    t0 t1 t2 t3 t4 t5 t6 t7
    s0 s1 s2 s3 s4 s5 s6 s7
    t8 t9
    k0 k1
    gp
    sp
    fp
    ra
];

const MUL_DIV_REG_NAMES: ([&str; 2], [&str; 2]) = reg_names![lo hi];

enum Reg {
    Lo = 32,
    Hi,
}

const NUM_REGS: usize = 32 + 2;

impl State {
    fn set(&mut self, r: usize, v: Use<Val>) {
        if r != 0 && r != NUM_REGS {
            self.regs[r] = v;
        }
    }
}

impl Isa for Mips32 {
    const ADDR_SIZE: BitSize = B32;

    fn default_regs(cx: &Cx<impl Platform<Isa = Self>>) -> Vec<Use<Val>> {
        let lower = (&GPR_NAMES.0, &MUL_DIV_REG_NAMES.0);
        let upper = (&GPR_NAMES.1, &MUL_DIV_REG_NAMES.1);
        [lower, upper]
            .iter()
            .enumerate()
            .flat_map(|(i, &(gpr_names, mul_div_reg_names))| {
                let base = i * NUM_REGS;
                iter::once(Val::Const(Const::new(B32, 0)))
                    .chain((1..32).map(move |i| {
                        Val::InReg(crate::ir::Reg {
                            index: base + i,
                            size: B32,
                            name: gpr_names[i],
                        })
                    }))
                    .chain(mul_div_reg_names.iter().enumerate().map(move |(i, name)| {
                        Val::InReg(crate::ir::Reg {
                            index: base + Reg::Lo as usize + i,
                            size: B32,
                            name,
                        })
                    }))
            })
            .map(|v| cx.a(v))
            .collect()
    }

    fn lift_instr(
        cx: &Cx<impl Platform<Isa = Self>>,
        pc: &mut Const,
        mut state: State,
    ) -> Result<State, Edges<Edge>> {
        macro_rules! error {
            ($($args:tt)*) => {
                return Err(Edges::One(Edge {
                    state,
                    effect: Effect::Error(format!($($args)*)),
                }))
            }
        }

        let instr = match cx.platform.rom().load(*pc, MemSize::M32) {
            Ok(x) => x.as_u32(),
            Err(e) => error!("failed to read ROM: {:?}", e),
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

        macro_rules! val {
            ($name:ident($($arg:expr),*)) => {
                cx.a(Val::$name($($arg),*))
            }
        }
        macro_rules! mem {
            ($name:ident($($arg:expr),*)) => {
                cx.a(Mem::$name($($arg),*))
            }
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
                match Self::lift_instr(cx, pc, state) {
                    Ok(state) => Err(Edges::One(Edge {
                        state,
                        effect: Effect::Jump(target),
                    })),
                    Err(Edges::One(Edge {
                        state,
                        effect: Effect::Opaque { call, next_pc: _ },
                    })) => {
                        // HACK(eddyb) replace the `next_pc` but reuse the `Opaque`.
                        Err(Edges::One(Edge {
                            state,
                            effect: Effect::Opaque {
                                call,
                                next_pc: target,
                            },
                        }))
                    }
                    Err(edges) => {
                        let effect = cx
                            .pretty_print_on_edges(edges.as_ref().map(|e, _| &e.effect))
                            .to_string();
                        // HACK(eddyb) extract some `state` for `error!`.
                        state = edges.map(|e, _| e.state).merge(|x, _| x);
                        error!("jump delay slot had effect: {}", effect);
                    }
                }
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
                match Self::lift_instr(cx, pc, state) {
                    Ok(state) => Err(Edges::Branch {
                        cond,
                        t: Edge { state: state.clone(), effect: Effect::Jump(t) },
                        e: Edge { state, effect: Effect::Jump(e) },
                    }),
                    Err(Edges::One(Edge {
                        state,
                        effect: Effect::Opaque { call, next_pc: _ },
                    })) => {
                        // HACK(eddyb) replace the `next_pc` but reuse the `Opaque`.
                        // NOTE(eddyb) this is even worse than the `jump!` one,
                        // because it duplicates the `Opaque`.
                        Err(Edges::Branch {
                            cond,
                            t: Edge {
                                state: state.clone(),
                                effect: Effect::Opaque {
                                    call: call.clone(),
                                    next_pc: t,
                                },
                            },
                            e: Edge {
                                state,
                                effect: Effect::Opaque {
                                    call,
                                    next_pc: e,
                                },
                            },
                        })
                    }
                    Err(edges) => {
                        let effect = cx.pretty_print_on_edges(
                            edges.as_ref().map(|e, _| &e.effect),
                        ).to_string();
                        // HACK(eddyb) extract some `state` for `error!`.
                        state = edges.map(|e, _| e.state).merge(|x, _| x);
                        error!("branch delay slot had effect: {}", effect);
                    }
                }
            }};
            ($cond:expr => $b:expr) => {
                branch!($cond => $b, branch_target!(), cx.a(add4(*pc)))
            };
        }

        let mut size = B32;
        macro_rules! get_reg_maybe64 {
            ($i:expr) => {{
                let i = $i as usize;
                match size {
                    B64 => val!(Int(
                        IntOp::Or,
                        B64,
                        val!(Int(
                            IntOp::Shl,
                            B64,
                            val!(Zext(B64, state.regs[NUM_REGS + i])),
                            cx.a(Const::new(B8, 32))
                        )),
                        val!(Zext(B64, state.regs[i]))
                    )),
                    B32 => state.regs[i],
                    _ => unreachable!(),
                }
            }};
        }
        macro_rules! set_reg_maybe64 {
            ($i:expr, $val:expr) => {{
                let i = $i as usize;
                let val = $val;
                match size {
                    B64 => {
                        state.set(i, val!(Trunc(B32, val)));
                        state.set(
                            NUM_REGS + i,
                            val!(Trunc(
                                B32,
                                val!(Int(IntOp::ShrU, B64, val, cx.a(Const::new(B8, 32))))
                            )),
                        );
                    }
                    B32 => state.set(i, val),
                    _ => unreachable!(),
                }
            }};
        }

        if op == 0 {
            // SPECIAL (R format and syscall/break).
            let funct = field(0, 6);
            match funct {
                12 | 13 => {
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::Opaque {
                            call: format!(
                                "{}(code={})",
                                if funct == 12 { "syscall" } else { "break" },
                                field(6, 20)
                            ),
                            next_pc: cx.a(*pc),
                        },
                    }));
                }
                _ => {}
            }

            if let 20 | 22 | 23 | 28..=31 | 44..=47 | 56 | 58..=60 | 62 | 63 = funct {
                // HACK(eddyb) force `{get,set}_reg_maybe64` below into 64-bit mode.
                size = B64;
            }

            if let 16..=19 = funct {
                // HACK(eddyb) unlike the above, these aren't 64-bit instructions,
                // but the whole value does need to be copied, in case it's used.
                size = B64;
            }

            let rs = get_reg_maybe64!(rs);
            let rt = get_reg_maybe64!(rt);
            let sa = field(6, 5);
            let v = match funct {
                0 => val!(Int(IntOp::Shl, B32, rt, cx.a(Const::new(B32, sa as u64)))),
                2 => val!(Int(IntOp::ShrU, B32, rt, cx.a(Const::new(B32, sa as u64)))),
                3 => val!(Int(IntOp::ShrS, B32, rt, cx.a(Const::new(B32, sa as u64)))),

                8 => return jump!(rs),
                9 => {
                    link!(rd);
                    return jump!(rs);
                }

                16 => get_reg_maybe64!(Reg::Hi as usize),
                17 => {
                    set_reg_maybe64!(Reg::Hi as usize, rs);
                    return Ok(state);
                }
                18 => get_reg_maybe64!(Reg::Lo as usize),
                19 => {
                    set_reg_maybe64!(Reg::Lo as usize, rs);
                    return Ok(state);
                }

                26 | 30 => {
                    set_reg_maybe64!(Reg::Lo as usize, val!(Int(IntOp::DivS, size, rs, rt)));
                    set_reg_maybe64!(Reg::Hi as usize, val!(Int(IntOp::RemS, size, rs, rt)));
                    return Ok(state);
                }

                27 | 31 => {
                    set_reg_maybe64!(Reg::Lo as usize, val!(Int(IntOp::DivU, size, rs, rt)));
                    set_reg_maybe64!(Reg::Hi as usize, val!(Int(IntOp::RemU, size, rs, rt)));
                    return Ok(state);
                }

                28 | 29 => {
                    // FIXME(eddyb) perform actual 128-bit multiplies, using
                    // `Sext(B128, ...)` for `funct=28`, and `Zext(B128, ...)`
                    // for `funct=29`, or emulate it using 64-bit operations only.
                    let result = val!(Int(IntOp::Mul, size, rs, rt));
                    set_reg_maybe64!(Reg::Lo as usize, result);
                    set_reg_maybe64!(Reg::Hi as usize, cx.a(Const::new(size, 0)));
                    return Ok(state);
                }

                32 | 33 => val!(Int(IntOp::Add, B32, rs, rt)),
                34 | 35 => val!(int_sub(rs, rt)),
                36 => val!(Int(IntOp::And, B32, rs, rt)),
                37 => val!(Int(IntOp::Or, B32, rs, rt)),
                38 => val!(Int(IntOp::Xor, B32, rs, rt)),
                39 => val!(bit_not(val!(Int(IntOp::Or, B32, rs, rt)))),
                42 => val!(Zext(B32, val!(Int(IntOp::LtS, B32, rs, rt)))),
                43 => val!(Zext(B32, val!(Int(IntOp::LtU, B32, rs, rt)))),

                60 => val!(Int(
                    IntOp::Shl,
                    size,
                    rt,
                    cx.a(Const::new(B8, sa as u64 + 32))
                )),
                63 => val!(Int(
                    IntOp::ShrU,
                    size,
                    rt,
                    cx.a(Const::new(B8, sa as u64 + 32))
                )),

                _ => error!("unknown SPECIAL funct={}", funct),
            };
            set_reg_maybe64!(rd, v);
        } else if op == 1 {
            // REGIMM (I format w/o rt).
            let rs = state.regs[rs];
            match rt {
                0 => return branch!(val!(Int(IntOp::LtS, B32, rs, zero)) => true),
                1 => return branch!(val!(Int(IntOp::LtS, B32, rs, zero)) => false),
                _ => error!("unknown REGIMM rt={}", rt),
            }
        } else if op == 2 || op == 3 {
            // J format.
            if op == 3 {
                link!();
            }
            return jump!(cx.a(Const::new(
                B32,
                ((pc.as_u32() & 0xc000_0000) | (field(0, 26) << 2)) as u64
            )));
        } else if (op, rs, rt) == (4, 0, 0) {
            // Special-case `zero == zero` branches to jumps.
            // HACK(eddyb) this is done here to avoid const-folding
            // away control-flow in the general case.
            return jump!(branch_target!());
        } else if op == 16 || op == 17 || op == 18 {
            // COPz.
            let cp = op - 16;
            let funct = field(0, 6);
            // FIXME(eddyb) implement basic floating-point instructions.
            if cp == 1 {
                return Err(Edges::One(Edge {
                    state,
                    effect: Effect::Opaque {
                        call: format!("COP1_FPU(rs={}, rt={}, rd={}, funct={})", rs, rt, rd, funct),
                        next_pc: cx.a(*pc),
                    },
                }));
            }

            // FIXME(eddyb) ssupport EPC, moves to/from it, and ERET.
            if cp == 0 && rs == 16 && funct == 24 {
                error!("ERET");
            }

            return Err(Edges::One(Edge {
                state,
                effect: Effect::Opaque {
                    call: format!(
                        "COP{}(rs={}, rt={}, rd={}, funct={})",
                        cp, rs, rt, rd, funct,
                    ),
                    next_pc: cx.a(*pc),
                },
            }));
        } else {
            // I format.

            if let 24..=27 | 39 | 44 | 45 | 52 | 55 | 60 | 63 = op {
                // HACK(eddyb) force `{get,set}_reg_maybe64` below into 64-bit mode.
                size = B64;
            }

            let rd = rt;
            let rs = state.regs[rs];
            let rt = get_reg_maybe64!(rt);

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
                // FIXME(eddyb) for 20..=23, only execute the delay slot when
                // the branch is taken (the specs talk about "nullification").
                4 | 20 => return branch!(val!(Int(IntOp::Eq, B32, rs, rt)) => true),
                5 | 21 => return branch!(val!(Int(IntOp::Eq, B32, rs, rt)) => false),
                6 | 22 => return branch!(val!(Int(IntOp::LtS, B32, zero, rs)) => false),
                7 | 23 => return branch!(val!(Int(IntOp::LtS, B32, zero, rs)) => true),

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

                47 => {
                    // FIXME(eddyb) use the result of rs+imm as an argument.
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::Opaque {
                            call: format!(
                                "CACHE(op={}, base={}, imm={:?})",
                                field(16, 5),
                                GPR_NAMES.0[field(21, 5) as usize],
                                imm,
                            ),
                            next_pc: cx.a(*pc),
                        },
                    }));
                }

                // FIXME(eddyb) implement basic floating-point instructions.
                49 | 53 | 57 | 61 => {
                    // FIXME(eddyb) use the result of rs+imm as an argument.
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::Opaque {
                            call: format!(
                                "{}{}C1_FPU(f{}, base={}, imm={:?})",
                                if (op & 8) == 0 { 'L' } else { 'S' },
                                if (op & 4) == 0 { 'W' } else { 'D' },
                                rd,
                                GPR_NAMES.0[field(21, 5) as usize],
                                imm
                            ),
                            next_pc: cx.a(*pc),
                        },
                    }));
                }

                55 => set_reg_maybe64!(rd, val!(Load(mem_ref!(M64)))),
                63 => state.mem = mem!(Store(mem_ref!(M64), rt)),

                _ => error!("unknown opcode 0x{:x} ({0})", op),
            }
        }

        Ok(state)
    }
}

use crate::ir::{
    BitSize::{self, *},
    Const, Cx, Edge, Edges, Effect, INode, IntOp, MemRef, MemSize, Node, State, Type,
};
use crate::isa::Isa;
use crate::platform::Rom;

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
        [$(stringify!($name)),*]
    }
}

const GPR_NAMES: [&str; 32] = reg_names![
    zero__THIS_SHOULD_NEVER_BE_USED
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

enum Reg {
    Lo = 32,
    Hi,
}

const NUM_REGS: usize = 32 + 2;

// FIXME(eddyb) make a `State` wrapper to contain these helpers.
impl State {
    fn get_mips32(&self, cx: &Cx, r: usize) -> INode {
        if r == 0 || r == NUM_REGS {
            cx.a(Const::new(B32, 0))
        } else {
            self.get(cx, self.reg_defs[r])
        }
    }

    fn set_mips32(&mut self, cx: &Cx, r: usize, v: INode) {
        if r != 0 && r != NUM_REGS {
            self.set(cx, self.reg_defs[r], v);
        }
    }
}

impl Isa for Mips32 {
    fn addr_size(&self) -> BitSize {
        B32
    }

    fn regs(&self, cx: &Cx) -> Vec<crate::ir::Reg> {
        [None, Some("upper")]
            .iter()
            .flat_map(|&suffix| {
                GPR_NAMES
                    .iter()
                    .chain(&["lo", "hi"])
                    .map(move |&name| match suffix {
                        None => cx.a(name),
                        Some(suffix) => cx.a(&format!("{}.{}", name, suffix)[..]),
                    })
            })
            .enumerate()
            .map(move |(index, name)| crate::ir::Reg {
                index,
                size: B32,
                name,
            })
            .collect()
    }

    fn lift_instr(
        &self,
        cx: &Cx,
        rom: &dyn Rom,
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

        let instr = match rom.load(*pc, MemSize::M32) {
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

        macro_rules! node {
            ($name:ident($($arg:expr),*)) => {
                cx.a(Node::$name($($arg),*))
            }
        }

        macro_rules! link {
            ($r:expr) => {
                state.set_mips32(cx, $r, cx.a(add4(*pc)))
            };
            () => {
                link!(31)
            };
        }
        macro_rules! jump {
            ($target:expr) => {{
                let target = $target;
                // Process delay slot.
                match self.lift_instr(cx, rom, pc, state) {
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

                assert_eq!(cx[cond].ty(cx), Type::Bits(B1));

                // Process delay slot.
                match self.lift_instr(cx, rom, pc, state) {
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
                    B64 => node!(Int(
                        IntOp::Or,
                        B64,
                        node!(Int(
                            IntOp::Shl,
                            B64,
                            node!(Zext(B64, state.get_mips32(cx, NUM_REGS + i))),
                            cx.a(Const::new(B8, 32))
                        )),
                        node!(Zext(B64, state.get_mips32(cx, i)))
                    )),
                    B32 => state.get_mips32(cx, i),
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
                        state.set_mips32(cx, i, node!(Trunc(B32, val)));
                        state.set_mips32(
                            cx,
                            NUM_REGS + i,
                            node!(Trunc(
                                B32,
                                node!(Int(IntOp::ShrU, B64, val, cx.a(Const::new(B8, 32))))
                            )),
                        );
                    }
                    B32 => state.set_mips32(cx, i, val),
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
                0 => node!(Int(IntOp::Shl, B32, rt, cx.a(Const::new(B32, sa as u64)))),
                2 => node!(Int(IntOp::ShrU, B32, rt, cx.a(Const::new(B32, sa as u64)))),
                3 => node!(Int(IntOp::ShrS, B32, rt, cx.a(Const::new(B32, sa as u64)))),

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
                    set_reg_maybe64!(Reg::Lo as usize, node!(Int(IntOp::DivS, size, rs, rt)));
                    set_reg_maybe64!(Reg::Hi as usize, node!(Int(IntOp::RemS, size, rs, rt)));
                    return Ok(state);
                }

                27 | 31 => {
                    set_reg_maybe64!(Reg::Lo as usize, node!(Int(IntOp::DivU, size, rs, rt)));
                    set_reg_maybe64!(Reg::Hi as usize, node!(Int(IntOp::RemU, size, rs, rt)));
                    return Ok(state);
                }

                28 | 29 => {
                    // FIXME(eddyb) perform actual 128-bit multiplies, using
                    // `Sext(B128, ...)` for `funct=28`, and `Zext(B128, ...)`
                    // for `funct=29`, or emulate it using 64-bit operations only.
                    let result = node!(Int(IntOp::Mul, size, rs, rt));
                    set_reg_maybe64!(Reg::Lo as usize, result);
                    set_reg_maybe64!(Reg::Hi as usize, cx.a(Const::new(size, 0)));
                    return Ok(state);
                }

                32 | 33 => node!(Int(IntOp::Add, B32, rs, rt)),
                34 | 35 => node!(int_sub(rs, rt)),
                36 => node!(Int(IntOp::And, B32, rs, rt)),
                37 => node!(Int(IntOp::Or, B32, rs, rt)),
                38 => node!(Int(IntOp::Xor, B32, rs, rt)),
                39 => node!(bit_not(node!(Int(IntOp::Or, B32, rs, rt)))),
                42 => node!(Zext(B32, node!(Int(IntOp::LtS, B32, rs, rt)))),
                43 => node!(Zext(B32, node!(Int(IntOp::LtU, B32, rs, rt)))),

                60 => node!(Int(
                    IntOp::Shl,
                    size,
                    rt,
                    cx.a(Const::new(B8, sa as u64 + 32))
                )),
                63 => node!(Int(
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
            let rs = state.get_mips32(cx, rs);
            match rt {
                0 => {
                    return branch!(node!(Int(IntOp::LtS, B32, rs, cx.a(Const::new(B32, 0)))) => true)
                }
                1 => {
                    return branch!(node!(Int(IntOp::LtS, B32, rs, cx.a(Const::new(B32, 0)))) => false)
                }
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
            let rs = state.get_mips32(cx, rs);
            let rt = get_reg_maybe64!(rt);

            macro_rules! mem_ref {
                ($sz:ident) => {
                    MemRef {
                        mem: state.get_mem(cx),
                        addr: node!(Int(IntOp::Add, B32, rs, cx.a(imm))),
                        size: MemSize::$sz,
                    }
                };
            }

            match op {
                // FIXME(eddyb) for 20..=23, only execute the delay slot when
                // the branch is taken (the specs talk about "nullification").
                4 | 20 => return branch!(node!(Int(IntOp::Eq, B32, rs, rt)) => true),
                5 | 21 => return branch!(node!(Int(IntOp::Eq, B32, rs, rt)) => false),
                6 | 22 => {
                    return branch!(node!(Int(IntOp::LtS, B32, cx.a(Const::new(B32, 0)), rs)) => false)
                }
                7 | 23 => {
                    return branch!(node!(Int(IntOp::LtS, B32, cx.a(Const::new(B32, 0)), rs)) => true)
                }

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

                    let mut v = node!(Int(op, B32, rs, cx.a(imm)));
                    if cx[v].ty(cx) == Type::Bits(B1) {
                        v = node!(Zext(B32, v));
                    }
                    state.set_mips32(cx, rd, v);
                }
                15 => state.set_mips32(cx, rd, cx.a(Const::new(B32, (imm.as_u32() << 16) as u64))),

                32 => state.set_mips32(cx, rd, node!(Sext(B32, node!(Load(mem_ref!(M8)))))),
                33 => state.set_mips32(cx, rd, node!(Sext(B32, node!(Load(mem_ref!(M16)))))),
                35 => state.set_mips32(cx, rd, node!(Load(mem_ref!(M32)))),
                36 => state.set_mips32(cx, rd, node!(Zext(B32, node!(Load(mem_ref!(M8)))))),
                37 => state.set_mips32(cx, rd, node!(Zext(B32, node!(Load(mem_ref!(M16)))))),

                40 => state.set_mem(cx, node!(Store(mem_ref!(M8), node!(Trunc(B8, rt))))),
                41 => state.set_mem(cx, node!(Store(mem_ref!(M16), node!(Trunc(B16, rt))))),
                43 => state.set_mem(cx, node!(Store(mem_ref!(M32), rt))),

                47 => {
                    // FIXME(eddyb) use the result of rs+imm as an argument.
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::Opaque {
                            call: format!(
                                "CACHE(op={}, base={}, imm={:?})",
                                field(16, 5),
                                GPR_NAMES[field(21, 5) as usize],
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
                                GPR_NAMES[field(21, 5) as usize],
                                imm
                            ),
                            next_pc: cx.a(*pc),
                        },
                    }));
                }

                55 => set_reg_maybe64!(rd, node!(Load(mem_ref!(M64)))),
                63 => state.set_mem(cx, node!(Store(mem_ref!(M64), rt))),

                _ => error!("unknown opcode 0x{:x} ({0})", op),
            }
        }

        Ok(state)
    }
}

use crate::ir::{
    BitSize::*, Const, Cx, Edge, Edges, Effect, Global, IGlobal, INode, IntOp, MemRef, MemSize,
    MemType, Node, State, Type,
};
use crate::isa::Isa;
use crate::platform::Rom;
use std::ops::Index;

pub struct I8051 {
    mem: IGlobal,
    rom: IGlobal,
    ext: IGlobal,
    regs: Regs,
}

impl I8051 {
    const ROM_MEM_TYPE: MemType = MemType {
        addr_size: B16,
        big_endian: false,
    };

    pub fn new(cx: &Cx) -> Self {
        I8051 {
            mem: cx.a(Global {
                ty: Type::Mem(MemType {
                    addr_size: B8,
                    big_endian: false,
                }),
                name: cx.a("m"),
            }),
            rom: cx.a(Global {
                ty: Type::Mem(Self::ROM_MEM_TYPE),
                name: cx.a("rom"),
            }),
            ext: cx.a(Global {
                ty: Type::Mem(MemType {
                    addr_size: B16,
                    big_endian: false,
                }),
                name: cx.a("ext"),
            }),
            regs: Regs::new(cx),
        }
    }
}

struct Regs {
    // FIXME(eddyb) use an array, or separate fields.
    // FIXME(eddyb) don't make every SFR a register, if reads are not
    // "pure", e.g. they interact with I/O, they should use special ops.
    sfr: Vec<IGlobal>,
    psw_c: IGlobal,
}

enum Sfr {
    SP = 0x01,
    DPL = 0x02,
    DPH = 0x03,
    PSW = 0x50,
    A = 0x60,
    B = 0x70,
}

impl Regs {
    fn new(cx: &Cx) -> Self {
        let reg = |size, name| {
            cx.a(Global {
                ty: Type::Bits(size),
                name,
            })
        };

        Regs {
            sfr: (0..0x80)
                .map(|i| {
                    cx.a(if i == Sfr::SP as usize {
                        "sp"
                    } else if i == Sfr::DPL as usize {
                        "dpl"
                    } else if i == Sfr::DPH as usize {
                        "dph"
                    } else if i == Sfr::PSW as usize {
                        "psw"
                    } else if i == Sfr::A as usize {
                        "a"
                    } else if i == Sfr::B as usize {
                        "b"
                    } else {
                        return cx.a(&format!("sfr_{:02x}", i)[..]);
                    })
                })
                .map(|name| reg(B8, name))
                .collect(),
            psw_c: reg(B1, cx.a("psw.c")),
        }
    }
}

impl Index<Sfr> for Regs {
    type Output = IGlobal;

    fn index(&self, r: Sfr) -> &IGlobal {
        &self.sfr[r as usize]
    }
}

impl Isa for I8051 {
    fn mem_containing_rom(&self) -> IGlobal {
        self.rom
    }

    fn lift_instr(
        &self,
        cx: &Cx,
        rom: &dyn Rom,
        pc: &mut Const,
        mut state: State,
    ) -> Result<State, Edges<Edge>> {
        let add1 = |x| IntOp::Add.eval(x, Const::new(x.size, 1)).unwrap();

        macro_rules! error {
            ($($args:tt)*) => {
                return Err(Edges::One(Edge {
                    state,
                    effect: Effect::Error(format!($($args)*)),
                }))
            }
        }

        macro_rules! imm {
            (8) => {{
                let v = match rom.load(Self::ROM_MEM_TYPE, *pc, MemSize::M8) {
                    Ok(v) => v,
                    Err(e) => error!("failed to read ROM: {:?}", e),
                };
                *pc = add1(*pc);
                v
            }};
            (16) => {
                Const::new(B16, (imm!(8).as_u64() << 8) | imm!(8).as_u64())
            };
        }

        let op = imm!(8).as_u8();

        macro_rules! node {
            ($name:ident($($arg:expr),*)) => {
                cx.a(Node::$name($($arg),*))
            }
        }
        macro_rules! mem_ref {
            ($addr:expr, $sz:ident) => {
                MemRef {
                    mem: state.get(cx, self.mem),
                    mem_type: cx[self.mem].ty.mem().unwrap(),
                    addr: $addr,
                    size: MemSize::$sz,
                }
            };
            ($addr:expr) => {
                mem_ref!($addr, M8)
            };
        }

        macro_rules! push {
            ($value:expr) => {{
                let value = $value;
                let size = cx[value].ty(cx).bit_size().unwrap();
                let sp = node!(Int(
                    IntOp::Add,
                    B8,
                    state.get(cx, self.regs[Sfr::SP]),
                    cx.a(Const::new(B8, (size.bits() / 8) as u64))
                ));
                state.set(cx, self.regs[Sfr::SP], sp);
                state.set(
                    cx,
                    self.mem,
                    node!(Store(
                        match size {
                            B8 => mem_ref!(sp),
                            B16 => mem_ref!(sp, M16),
                            _ => unreachable!(),
                        },
                        value
                    )),
                );
            }};
        }

        macro_rules! pop {
            ($sz:ident) => {{
                let sp = state.get(cx, self.regs[Sfr::SP]);
                let value = node!(Load(mem_ref!(sp, $sz)));
                state.set(
                    cx,
                    self.regs[Sfr::SP],
                    node!(int_sub(
                        sp,
                        cx.a(Const::new(B8, MemSize::$sz.bytes() as u64))
                    )),
                );
                value
            }};
        }

        macro_rules! get_dptr {
            () => {
                node!(Int(
                    IntOp::Or,
                    B16,
                    node!(Int(
                        IntOp::Shl,
                        B16,
                        node!(Zext(B16, state.get(cx, self.regs[Sfr::DPH]))),
                        cx.a(Const::new(B8, 8))
                    )),
                    node!(Zext(B16, state.get(cx, self.regs[Sfr::DPL])))
                ))
            };
        }

        macro_rules! jump {
            ($target:expr) => {
                Err(Edges::One(Edge {
                    effect: Effect::Jump($target),
                    state,
                }))
            };
        }
        macro_rules! call {
            ($target:expr) => {{
                let target = $target;
                push!(cx.a(*pc));
                jump!(target)
            }};
        }
        macro_rules! relative_target {
            () => {{
                let offset = imm!(8).sext(B16);
                cx.a(IntOp::Add.eval(*pc, offset).unwrap())
            }};
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

                Err(Edges::Branch {
                    cond,
                    t: Edge { state: state.clone(), effect: Effect::Jump(t) },
                    e: Edge { state: state, effect: Effect::Jump(e) },
                })
            }};
            ($cond:expr => $b:expr) => {
                branch!($cond => $b, relative_target!(), cx.a(*pc))
            };
        }

        if op == 0xa5 {
            error!("reserved opcode 0x{:x}", op);
        }

        if (op & 0xf) == 1 {
            let addr11 = (((op >> 5) as u16) << 8) | imm!(8).as_u16();
            let target = cx.a(Const::new(B16, ((pc.as_u16() & 0xf800) | addr11) as u64));
            if (op & 0x10) == 0 {
                return jump!(target);
            } else {
                return call!(target);
            }
        }

        enum Operand {
            Imm(Const),
            Sfr(u8),
            Mem(IGlobal, INode),
        }

        let operand;

        macro_rules! get {
            ($operand:expr) => {
                match $operand {
                    Operand::Imm(x) => cx.a(x),
                    Operand::Sfr(i) => {
                        // FIXME(eddyb) emulate `PSW` reads by composing it out of bits.
                        assert!(i != Sfr::PSW as u8);
                        state.get(cx, self.regs.sfr[i as usize])
                    }
                    Operand::Mem(mem, addr) => node!(Load(MemRef {
                        mem: state.get(cx, mem),
                        mem_type: cx[mem].ty.mem().unwrap(),
                        addr,
                        size: MemSize::M8,
                    })),
                }
            };
            () => {
                get!(operand)
            };
        }
        macro_rules! set {
            ($operand:expr, $val:expr) => {{
                let val = $val;
                match $operand {
                    Operand::Imm(_) => unreachable!(),
                    Operand::Sfr(i) => {
                        // FIXME(eddyb) emulate `PSW` writes by splitting it into bits.
                        assert!(i != Sfr::PSW as u8);
                        state.set(cx, self.regs.sfr[i as usize], val);
                    }
                    Operand::Mem(mem, addr) => state.set(
                        cx,
                        mem,
                        node!(Store(
                            MemRef {
                                mem: state.get(cx, mem),
                                mem_type: cx[mem].ty.mem().unwrap(),
                                addr,
                                size: MemSize::M8,
                            },
                            val
                        )),
                    ),
                }
            }};
            ($val:expr) => {
                set!(operand, $val)
            };
        }
        macro_rules! direct {
            () => {{
                let addr = imm!(8);
                if addr.as_u8() > 0x80 {
                    Operand::Sfr(addr.as_u8() & 0x7f)
                } else {
                    Operand::Mem(self.mem, cx.a(addr))
                }
            }};
        }

        if (op & 0xf) >= 4 {
            operand = if (op & 0xf) == 4 {
                match op >> 4 {
                    0..=1 | 7..=8 | 0xa | 0xc..=0xf => Operand::Sfr(Sfr::A as u8),
                    2..=6 | 9 | 0xb => Operand::Imm(imm!(8)),
                    _ => unreachable!(),
                }
            } else if (op & 0xf) == 5 {
                direct!()
            } else {
                Operand::Mem(
                    self.mem,
                    if (op & 0xf) < 8 {
                        node!(Load(mem_ref!(cx.a(Const::new(B8, (op & 1) as u64)))))
                    } else {
                        cx.a(Const::new(B8, (op & 7) as u64))
                    },
                )
            };

            match op >> 4 {
                0 => {
                    set!(node!(Int(IntOp::Add, B8, get!(), cx.a(Const::new(B8, 1)))));
                }
                1 => {
                    set!(node!(int_sub(get!(), cx.a(Const::new(B8, 1)))));
                }
                2 => {
                    let (a, b) = (state.get(cx, self.regs[Sfr::A]), get!());
                    // HACK(eddyb) this computes the result & carry by
                    // doing the operation with 16 bits instead of 8.
                    let wide = node!(Int(
                        IntOp::Add,
                        B16,
                        node!(Zext(B16, a)),
                        node!(Zext(B16, b))
                    ));
                    state.set(cx, self.regs[Sfr::A], node!(Trunc(B8, wide)));
                    state.set(
                        cx,
                        self.regs.psw_c,
                        node!(Trunc(
                            B1,
                            node!(Int(IntOp::ShrU, B16, wide, cx.a(Const::new(B8, 8))))
                        )),
                    );
                }
                3 => {
                    let (a, b) = (state.get(cx, self.regs[Sfr::A]), get!());
                    // HACK(eddyb) this computes the result & carry by
                    // doing the operation with 16 bits instead of 8.
                    let wide = node!(Int(
                        IntOp::Add,
                        B16,
                        node!(Int(
                            IntOp::Add,
                            B16,
                            node!(Zext(B16, a)),
                            node!(Zext(B16, b))
                        )),
                        node!(Zext(B16, state.get(cx, self.regs.psw_c)))
                    ));
                    state.set(cx, self.regs[Sfr::A], node!(Trunc(B8, wide)));
                    state.set(
                        cx,
                        self.regs.psw_c,
                        node!(Trunc(
                            B1,
                            node!(Int(IntOp::ShrU, B16, wide, cx.a(Const::new(B8, 8))))
                        )),
                    );
                }
                4 => {
                    state.set(
                        cx,
                        self.regs[Sfr::A],
                        node!(Int(IntOp::Or, B8, state.get(cx, self.regs[Sfr::A]), get!())),
                    );
                }
                5 => {
                    state.set(
                        cx,
                        self.regs[Sfr::A],
                        node!(Int(
                            IntOp::And,
                            B8,
                            state.get(cx, self.regs[Sfr::A]),
                            get!()
                        )),
                    );
                }
                6 => {
                    state.set(
                        cx,
                        self.regs[Sfr::A],
                        node!(Int(
                            IntOp::Xor,
                            B8,
                            state.get(cx, self.regs[Sfr::A]),
                            get!()
                        )),
                    );
                }
                7 => set!(cx.a(imm!(8))),
                8 if op == 0x84 => {
                    let a = state.get(cx, self.regs[Sfr::A]);
                    let b = state.get(cx, self.regs[Sfr::B]);
                    let (a, b) = (
                        node!(Int(IntOp::DivU, B8, a, b)),
                        node!(Int(IntOp::RemU, B8, a, b)),
                    );
                    state.set(cx, self.regs[Sfr::A], a);
                    state.set(cx, self.regs[Sfr::B], b);
                }
                8 => set!(direct!(), get!()),
                9 => {
                    state.set(
                        cx,
                        self.regs[Sfr::A],
                        node!(int_sub(
                            node!(int_sub(state.get(cx, self.regs[Sfr::A]), get!())),
                            node!(Zext(B8, state.get(cx, self.regs.psw_c)))
                        )),
                    );
                    // FIXME(eddyb) set the carry bit.
                }
                0xa if op == 0xa4 => {
                    let a = state.get(cx, self.regs[Sfr::A]);
                    let b = state.get(cx, self.regs[Sfr::B]);
                    let (a, b) = (
                        node!(Int(IntOp::Mul, B8, a, b)),
                        node!(Trunc(
                            B8,
                            node!(Int(
                                IntOp::ShrU,
                                B16,
                                node!(Int(
                                    IntOp::Mul,
                                    B16,
                                    node!(Zext(B16, a)),
                                    node!(Zext(B16, b))
                                )),
                                cx.a(Const::new(B8, 8))
                            ))
                        )),
                    );
                    state.set(cx, self.regs[Sfr::A], a);
                    state.set(cx, self.regs[Sfr::B], b);
                }
                0xa => set!(get!(direct!())),
                0xb if op == 0xb4 || op == 0xb5 => {
                    return branch!(node!(Int(IntOp::Eq, B8, get!(), state.get(cx, self.regs[Sfr::A]))) => false);
                }
                0xb => return branch!(node!(Int(IntOp::Eq, B8, get!(), cx.a(imm!(8)))) => false),
                0xc if op == 0xc4 => set!(node!(bit_rol(get!(), cx.a(Const::new(B8, 4))))),
                0xc => {
                    let a = state.get(cx, self.regs[Sfr::A]);
                    state.set(cx, self.regs[Sfr::A], get!());
                    set!(a);
                }
                0xd if op == 0xd4 => {
                    error!("unimplemented decimal adjust");
                }
                0xd if op == 0xd6 || op == 0xd7 => {
                    macro_rules! nibbles {
                        ($v:expr) => {{
                            let v = $v;
                            (
                                node!(Int(IntOp::And, B8, v, cx.a(Const::new(B8, 0xf0)))),
                                node!(Int(IntOp::And, B8, v, cx.a(Const::new(B8, 0x0f)))),
                            )
                        }};
                    }
                    let (a_hi, a_lo) = nibbles!(state.get(cx, self.regs[Sfr::A]));
                    let (v_hi, v_lo) = nibbles!(get!());
                    state.set(cx, self.regs[Sfr::A], node!(Int(IntOp::Or, B8, a_hi, v_lo)));
                    set!(node!(Int(IntOp::Or, B8, v_hi, a_lo)));
                }
                0xd => {
                    let val = node!(int_sub(get!(), cx.a(Const::new(B8, 1))));
                    set!(val);
                    return branch!(node!(Int(IntOp::Eq, B8, val, cx.a(Const::new(B8, 0)))) => false);
                }
                0xe if op == 0xe4 => set!(cx.a(Const::new(B8, 0))),
                0xe => state.set(cx, self.regs[Sfr::A], get!()),
                0xf if op == 0xf4 => set!(node!(bit_not(get!()))),
                0xf => set!(state.get(cx, self.regs[Sfr::A])),
                _ => unreachable!(),
            }
        } else {
            macro_rules! bit_addr {
                () => {{
                    let addr = imm!(8).as_u8();
                    let byte = addr >> 3;
                    let bit = addr & 7;
                    operand = if addr > 0x80 {
                        Operand::Sfr((byte << 3) & 0x7f)
                    } else {
                        Operand::Mem(self.mem, cx.a(Const::new(B8, (0x20 + byte) as u64)))
                    };
                    bit
                }};
            }

            match op {
                0x00 => {}
                0x02 => return jump!(cx.a(imm!(16))),
                0x03 | 0x13 => {
                    state.set(
                        cx,
                        self.regs[Sfr::A],
                        node!(bit_ror(
                            state.get(cx, self.regs[Sfr::A]),
                            cx.a(Const::new(B8, 1))
                        )),
                    );
                    if op == 0x13 {
                        // FIXME(eddyb) set (and read) the flags.
                    }
                }
                0x10 | 0x20 | 0x30 => {
                    let bit = bit_addr!();
                    let val = get!();
                    let bit_was_set =
                        node!(Int(IntOp::And, B8, val, cx.a(Const::new(B8, 1 << bit))));
                    if op == 0x10 {
                        set!(node!(Int(
                            IntOp::And,
                            B8,
                            val,
                            cx.a(Const::new(B8, (!(1u8 << bit)) as u64))
                        )));
                    }
                    return branch!(node!(Int(IntOp::Eq, B8, bit_was_set, cx.a(Const::new(B8, 0)))) => op == 0x30);
                }
                0x12 => return call!(cx.a(imm!(16))),
                0x22 | 0x32 => {
                    if op == 0x32 {
                        error!("unimplemented RETI");
                    }
                    return jump!(pop!(M16));
                }
                0x23 | 0x33 => {
                    state.set(
                        cx,
                        self.regs[Sfr::A],
                        node!(bit_rol(
                            state.get(cx, self.regs[Sfr::A]),
                            cx.a(Const::new(B8, 1))
                        )),
                    );
                    if op == 0x33 {
                        // FIXME(eddyb) set (and read) the flags.
                    }
                }
                0x40 | 0x50 => {
                    return branch!(node!(Int(IntOp::Eq, B1, state.get(cx, self.regs.psw_c), cx.a(Const::new(B1, 0)))) => op == 0x50);
                }
                0x60 | 0x70 => {
                    return branch!(node!(Int(IntOp::Eq, B8, state.get(cx, self.regs[Sfr::A]), cx.a(Const::new(B8, 0)))) => op == 0x60);
                }
                0x42 | 0x43 | 0x52 | 0x53 | 0x62 | 0x63 => {
                    operand = direct!();
                    set!(node!(Int(
                        match op >> 4 {
                            4 => IntOp::Or,
                            5 => IntOp::And,
                            6 => IntOp::Xor,
                            _ => unreachable!(),
                        },
                        B8,
                        get!(),
                        if (op & 0xf) == 2 {
                            state.get(cx, self.regs[Sfr::A])
                        } else {
                            cx.a(imm!(8))
                        }
                    )));
                }
                0x72 | 0x82 | 0xa0 | 0xa2 | 0xb0 => {
                    let bit = bit_addr!();
                    let val = node!(Trunc(
                        B1,
                        node!(Int(
                            IntOp::ShrU,
                            B8,
                            get!(),
                            cx.a(Const::new(B8, bit as u64))
                        ))
                    ));
                    state.set(
                        cx,
                        self.regs.psw_c,
                        match op {
                            0xa2 => val,

                            0x72 => node!(Int(IntOp::Or, B1, state.get(cx, self.regs.psw_c), val)),
                            0xa0 => node!(Int(
                                IntOp::Or,
                                B1,
                                state.get(cx, self.regs.psw_c),
                                node!(bit_not(val))
                            )),
                            0xb0 => node!(Int(
                                IntOp::And,
                                B1,
                                state.get(cx, self.regs.psw_c),
                                node!(bit_not(val))
                            )),
                            _ => unreachable!(),
                        },
                    )
                }
                0x73 | 0x83 | 0x93 => {
                    let base = if op == 0x83 { cx.a(*pc) } else { get_dptr!() };
                    let addr = node!(Int(
                        IntOp::Add,
                        B16,
                        base,
                        node!(Zext(B16, state.get(cx, self.regs[Sfr::A])))
                    ));
                    if op == 0x73 {
                        return jump!(addr);
                    } else {
                        state.set(cx, self.regs[Sfr::A], get!(Operand::Mem(self.rom, addr)));
                    }
                }
                0x80 => return jump!(relative_target!()),
                0x90 => {
                    state.set(cx, self.regs[Sfr::DPH], cx.a(imm!(8)));
                    state.set(cx, self.regs[Sfr::DPL], cx.a(imm!(8)));
                }
                0x92 => {
                    let bit = bit_addr!();
                    set!(node!(Int(
                        IntOp::Or,
                        B8,
                        get!(),
                        node!(Int(
                            IntOp::Shl,
                            B8,
                            node!(Zext(B8, state.get(cx, self.regs.psw_c))),
                            cx.a(Const::new(B8, bit as u64))
                        ))
                    )));
                }
                0xa3 => {
                    let v = node!(Int(IntOp::Add, B16, get_dptr!(), cx.a(Const::new(B16, 1))));
                    state.set(cx, self.regs[Sfr::DPL], node!(Trunc(B8, v)));
                    state.set(
                        cx,
                        self.regs[Sfr::DPH],
                        node!(Trunc(
                            B8,
                            node!(Int(IntOp::ShrU, B16, v, cx.a(Const::new(B8, 8))))
                        )),
                    );
                }
                0xb2 => {
                    let bit = bit_addr!();
                    set!(node!(Int(
                        IntOp::Xor,
                        B8,
                        get!(),
                        cx.a(Const::new(B8, 1 << bit))
                    )));
                }
                0xc0 => push!(get!(direct!())),
                0xc2 => {
                    let bit = bit_addr!();
                    set!(node!(Int(
                        IntOp::And,
                        B8,
                        get!(),
                        cx.a(Const::new(B8, (!(1u8 << bit)) as u64))
                    )));
                }
                0xc3 | 0xd3 => state.set(cx, self.regs.psw_c, cx.a(Const::from(op == 0xd3))),
                0xd0 => set!(direct!(), pop!(M8)),
                0xd2 => {
                    let bit = bit_addr!();
                    set!(node!(Int(
                        IntOp::Or,
                        B8,
                        get!(),
                        cx.a(Const::new(B8, 1 << bit))
                    )));
                }
                0xe0 | 0xe2 | 0xe3 | 0xf0 | 0xf2 | 0xf3 => {
                    operand = Operand::Mem(
                        self.ext,
                        if (op & 0xf) == 0 {
                            get_dptr!()
                        } else {
                            node!(Zext(
                                B16,
                                node!(Load(mem_ref!(cx.a(Const::new(B8, (op & 1) as u64)))))
                            ))
                        },
                    );
                    if (op & 0xf0) == 0xe0 {
                        state.set(cx, self.regs[Sfr::A], get!());
                    } else {
                        set!(state.get(cx, self.regs[Sfr::A]));
                    }
                }

                _ => error!("unsupported opcode 0x{:x}", op),
            }
        }

        Ok(state)
    }
}

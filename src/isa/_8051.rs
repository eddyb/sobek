// TODO(eddyb) use a better name for this module.

use crate::ir::{
    BitSize::{self, *},
    Const, Cx, Edge, Edges, Effect, IntOp, Isa, Mem, MemRef, MemSize, Platform, Rom, State, Use,
    Val,
};
use std::iter;

pub struct _8051;

// FIXME(eddyb) maybe replace `Reg` with enums like these.
enum Reg {
    SP = 0x01,
    DPL = 0x02,
    DPH = 0x03,
    PSW = 0x50,
    A = 0x60,
    B = 0x70,

    #[allow(non_camel_case_types)]
    PSW_C = 0x80,
}

// FIXME(eddyb) don't make every SFR a register, if reads are not
// "pure", e.g. they interact with I/O, they should use memory ops.

impl Isa for _8051 {
    // FIXME(eddyb) add proper support for a Harvard architecture.
    const ADDR_SIZE: BitSize = B16;

    fn default_regs(cx: &Cx<impl Platform<Isa = Self>>) -> Vec<Use<Val>> {
        (0..0x80)
            .map(|i| {
                crate::ir::Reg {
                    index: i,
                    size: B8,
                    name: if i == Reg::SP as usize {
                        "sp"
                    } else if i == Reg::DPL as usize {
                        "dpl"
                    } else if i == Reg::DPH as usize {
                        "dph"
                    } else if i == Reg::PSW as usize {
                        "psw"
                    } else if i == Reg::A as usize {
                        "a"
                    } else if i == Reg::B as usize {
                        "b"
                    } else {
                        // HACK(eddyb) leak a dynamically allocated string
                        // to avoid having to hardcode all the register names.
                        Box::leak(format!("sfr_{:02x}", i).into_boxed_str())
                    },
                }
            })
            .chain(iter::once(crate::ir::Reg {
                index: Reg::PSW_C as usize,
                size: B1,
                name: "psw.c",
            }))
            .map(|v| cx.a(Val::InReg(v)))
            .collect()
    }

    fn lift_instr(
        cx: &Cx<impl Platform<Isa = Self>>,
        pc: &mut Const,
        mut state: State,
    ) -> Result<State, Edges<Edge>> {
        let add1 = |x| IntOp::Add.eval(x, Const::new(x.size, 1)).unwrap();

        macro_rules! imm {
            (8) => {{
                let v = cx.platform.rom().load(*pc, MemSize::M8).unwrap();
                *pc = add1(*pc);
                v
            }};
            (16) => {
                Const::new(B16, (imm!(8).as_u64() << 8) | imm!(8).as_u64())
            };
        }

        let op = imm!(8).as_u8();

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
        macro_rules! mem_ref {
            ($addr:expr, $sz:ident) => {{
                let addr = $addr;
                assert_eq!(cx[addr].size(), B8);
                MemRef {
                    mem: state.mem,
                    addr,
                    size: MemSize::$sz,
                }
            }};
            ($addr:expr) => {
                mem_ref!($addr, M8)
            };
        }

        macro_rules! push {
            ($value:expr) => {{
                let value = $value;
                let size = cx[value].size();
                let sp = val!(Int(
                    IntOp::Add,
                    B8,
                    state.regs[Reg::SP as usize],
                    cx.a(Const::new(B8, (size.bits() / 8) as u64))
                ));
                state.regs[Reg::SP as usize] = sp;
                state.mem = mem!(Store(
                    match size {
                        B8 => mem_ref!(sp),
                        B16 => mem_ref!(sp, M16),
                        _ => unreachable!(),
                    },
                    value
                ));
            }};
        }

        macro_rules! pop {
            ($sz:ident) => {{
                let sp = state.regs[Reg::SP as usize];
                let value = val!(Load(mem_ref!(sp, $sz)));
                state.regs[Reg::SP as usize] = val!(int_sub(
                    sp,
                    cx.a(Const::new(B8, (MemSize::$sz.bits() / 8) as u64))
                ));
                value
            }};
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
                // FIXME(eddyb) impl `From<iN>` for `Const` already!
                let offset = Const::new(B16, imm!(8).as_i8() as i16 as u16 as u64);
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

                assert_eq!(cx[cond].size(), B1);

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
            panic!("8051: reserved opcode 0x{:x}", op);
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
            Reg(usize),
            Mem(MemRef),
        }

        let operand;

        macro_rules! get {
            ($operand:expr) => {
                match $operand {
                    Operand::Imm(x) => cx.a(x),
                    Operand::Reg(i) => {
                        // FIXME(eddyb) emulate `PSW` reads by composing it out of bits.
                        assert!(i != Reg::PSW as usize);
                        state.regs[i]
                    }
                    Operand::Mem(m) => val!(Load(m)),
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
                    Operand::Reg(i) => {
                        // FIXME(eddyb) emulate `PSW` writes by splitting it into bits.
                        assert!(i != Reg::PSW as usize);
                        state.regs[i] = val;
                    }
                    Operand::Mem(m) => state.mem = mem!(Store(m, val)),
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
                    Operand::Reg((addr.as_u8() & 0x7f) as usize)
                } else {
                    Operand::Mem(mem_ref!(cx.a(addr)))
                }
            }};
        }

        if (op & 0xf) >= 4 {
            operand = if (op & 0xf) == 4 {
                match op >> 4 {
                    0..=1 | 7..=8 | 0xa | 0xc..=0xf => Operand::Reg(Reg::A as usize),
                    2..=6 | 9 | 0xb => Operand::Imm(imm!(8)),
                    _ => unreachable!(),
                }
            } else if (op & 0xf) == 5 {
                direct!()
            } else {
                Operand::Mem(mem_ref!(if (op & 0xf) < 8 {
                    val!(Load(mem_ref!(cx.a(Const::new(B8, (op & 1) as u64)))))
                } else {
                    cx.a(Const::new(B8, (op & 7) as u64))
                }))
            };

            match op >> 4 {
                0 => {
                    set!(val!(Int(IntOp::Add, B8, get!(), cx.a(Const::new(B8, 1)))));
                }
                1 => {
                    set!(val!(int_sub(get!(), cx.a(Const::new(B8, 1)))));
                }
                2 => {
                    let (a, b) = (state.regs[Reg::A as usize], get!());
                    // HACK(eddyb) this computes the result & carry by
                    // doing the operation with 16 bits instead of 8.
                    let wide = val!(Int(IntOp::Add, B16, val!(Zext(B16, a)), val!(Zext(B16, b))));
                    state.regs[Reg::A as usize] = val!(Trunc(B8, wide));
                    state.regs[Reg::PSW_C as usize] = val!(Trunc(
                        B1,
                        val!(Int(IntOp::ShrU, B16, wide, cx.a(Const::new(B8, 8))))
                    ));
                }
                3 => {
                    let (a, b) = (state.regs[Reg::A as usize], get!());
                    // HACK(eddyb) this computes the result & carry by
                    // doing the operation with 16 bits instead of 8.
                    let wide = val!(Int(
                        IntOp::Add,
                        B16,
                        val!(Int(IntOp::Add, B16, val!(Zext(B16, a)), val!(Zext(B16, b)))),
                        val!(Zext(B16, state.regs[Reg::PSW_C as usize]))
                    ));
                    state.regs[Reg::A as usize] = val!(Trunc(B8, wide));
                    state.regs[Reg::PSW_C as usize] = val!(Trunc(
                        B1,
                        val!(Int(IntOp::ShrU, B16, wide, cx.a(Const::new(B8, 8))))
                    ));
                }
                4 => {
                    state.regs[Reg::A as usize] =
                        val!(Int(IntOp::Or, B8, state.regs[Reg::A as usize], get!()));
                }
                5 => {
                    state.regs[Reg::A as usize] =
                        val!(Int(IntOp::And, B8, state.regs[Reg::A as usize], get!()));
                }
                6 => {
                    state.regs[Reg::A as usize] =
                        val!(Int(IntOp::Xor, B8, state.regs[Reg::A as usize], get!()));
                }
                7 => set!(cx.a(imm!(8))),
                8 if op == 0x84 => {
                    let a = state.regs[Reg::A as usize];
                    let b = state.regs[Reg::B as usize];
                    let (a, b) = (
                        val!(Int(IntOp::DivU, B8, a, b)),
                        val!(Int(IntOp::RemU, B8, a, b)),
                    );
                    state.regs[Reg::A as usize] = a;
                    state.regs[Reg::B as usize] = b;
                }
                8 => set!(direct!(), get!()),
                9 => {
                    state.regs[Reg::A as usize] = val!(int_sub(
                        val!(int_sub(state.regs[Reg::A as usize], get!())),
                        val!(Zext(B8, state.regs[Reg::PSW_C as usize]))
                    ));
                    // FIXME(eddyb) set the carry bit.
                }
                0xa if op == 0xa4 => {
                    let a = state.regs[Reg::A as usize];
                    let b = state.regs[Reg::B as usize];
                    let (a, b) = (
                        val!(Int(IntOp::Mul, B8, a, b)),
                        val!(Trunc(
                            B8,
                            val!(Int(
                                IntOp::ShrU,
                                B16,
                                val!(Int(IntOp::Mul, B16, val!(Zext(B16, a)), val!(Zext(B16, b)))),
                                cx.a(Const::new(B8, 8))
                            ))
                        )),
                    );
                    state.regs[Reg::A as usize] = a;
                    state.regs[Reg::B as usize] = b;
                }
                0xa => set!(get!(direct!())),
                0xb if op == 0xb4 || op == 0xb5 => {
                    return branch!(val!(Int(IntOp::Eq, B8, get!(), state.regs[Reg::A as usize])) => false);
                }
                0xb => return branch!(val!(Int(IntOp::Eq, B8, get!(), cx.a(imm!(8)))) => false),
                0xc if op == 0xc4 => set!(val!(bit_rol(get!(), cx.a(Const::new(B8, 4))))),
                0xc => {
                    let a = state.regs[Reg::A as usize];
                    state.regs[Reg::A as usize] = get!();
                    set!(a);
                }
                0xd if op == 0xd4 => {
                    eprintln!("8051: decimal adjust");
                }
                0xd if op == 0xd6 || op == 0xd7 => {
                    macro_rules! nibbles {
                        ($v:expr) => {{
                            let v = $v;
                            (
                                val!(Int(IntOp::And, B8, v, cx.a(Const::new(B8, 0xf0)))),
                                val!(Int(IntOp::And, B8, v, cx.a(Const::new(B8, 0x0f)))),
                            )
                        }};
                    }
                    let (a_hi, a_lo) = nibbles!(state.regs[Reg::A as usize]);
                    let (v_hi, v_lo) = nibbles!(get!());
                    state.regs[Reg::A as usize] = val!(Int(IntOp::Or, B8, a_hi, v_lo));
                    set!(val!(Int(IntOp::Or, B8, v_hi, a_lo)));
                }
                0xd => {
                    let val = val!(int_sub(get!(), cx.a(Const::new(B8, 1))));
                    set!(val);
                    return branch!(val!(Int(IntOp::Eq, B8, val, cx.a(Const::new(B8, 0)))) => false);
                }
                0xe if op == 0xe4 => set!(cx.a(Const::new(B8, 0))),
                0xe => state.regs[Reg::A as usize] = get!(),
                0xf if op == 0xf4 => set!(val!(bit_not(get!()))),
                0xf => set!(state.regs[Reg::A as usize]),
                _ => unreachable!(),
            }
        } else {
            macro_rules! bit_addr {
                () => {{
                    let addr = imm!(8).as_u8();
                    let byte = addr >> 3;
                    let bit = addr & 7;
                    operand = if addr > 0x80 {
                        Operand::Reg(((byte << 3) & 0x7f) as usize)
                    } else {
                        Operand::Mem(mem_ref!(cx.a(Const::new(B8, (0x20 + byte) as u64))))
                    };
                    bit
                }};
            }

            match op {
                0x00 => {}
                0x02 => return jump!(cx.a(imm!(16))),
                0x03 => {
                    state.regs[Reg::A as usize] = val!(bit_ror(
                        state.regs[Reg::A as usize],
                        cx.a(Const::new(B8, 1))
                    ))
                }
                0x10 | 0x20 | 0x30 => {
                    let bit = bit_addr!();
                    let val = get!();
                    let bit_was_set =
                        val!(Int(IntOp::And, B8, val, cx.a(Const::new(B8, 1 << bit))));
                    if op == 0x10 {
                        set!(val!(Int(
                            IntOp::And,
                            B8,
                            val,
                            cx.a(Const::new(B8, (!(1u8 << bit)) as u64))
                        )));
                    }
                    return branch!(val!(Int(IntOp::Eq, B8, bit_was_set, cx.a(Const::new(B8, 0)))) => op == 0x30);
                }
                0x12 => return call!(cx.a(imm!(16))),
                0x22 | 0x32 => {
                    if op == 0x32 {
                        eprintln!("8051: RETI incomplete");
                    }
                    return jump!(pop!(M16));
                }
                0x23 => {
                    state.regs[Reg::A as usize] = val!(bit_rol(
                        state.regs[Reg::A as usize],
                        cx.a(Const::new(B8, 1))
                    ))
                }
                0x40 | 0x50 => {
                    return branch!(val!(Int(IntOp::Eq, B1, state.regs[Reg::PSW_C as usize], cx.a(Const::new(B1, 0)))) => op == 0x50);
                }
                0x60 | 0x70 => {
                    return branch!(val!(Int(IntOp::Eq, B8, state.regs[Reg::A as usize], cx.a(Const::new(B8, 0)))) => op == 0x60);
                }
                0x42 | 0x43 | 0x52 | 0x53 | 0x62 | 0x63 => {
                    operand = direct!();
                    set!(val!(Int(
                        match op >> 4 {
                            4 => IntOp::Or,
                            5 => IntOp::And,
                            6 => IntOp::Xor,
                            _ => unreachable!(),
                        },
                        B8,
                        get!(),
                        if (op & 0xf) == 2 {
                            state.regs[Reg::A as usize]
                        } else {
                            cx.a(imm!(8))
                        }
                    )));
                }
                0x72 | 0x82 | 0xa0 | 0xa2 | 0xb0 => {
                    let bit = bit_addr!();
                    let val = val!(Trunc(
                        B1,
                        val!(Int(
                            IntOp::ShrU,
                            B8,
                            get!(),
                            cx.a(Const::new(B8, bit as u64))
                        ))
                    ));
                    state.regs[Reg::PSW_C as usize] = match op {
                        0xa2 => val,

                        0x72 => val!(Int(IntOp::Or, B1, state.regs[Reg::PSW_C as usize], val)),
                        0xa0 => val!(Int(
                            IntOp::Or,
                            B1,
                            state.regs[Reg::PSW_C as usize],
                            val!(bit_not(val))
                        )),
                        0xb0 => val!(Int(
                            IntOp::And,
                            B1,
                            state.regs[Reg::PSW_C as usize],
                            val!(bit_not(val))
                        )),
                        _ => unreachable!(),
                    }
                }
                0x73 | 0x83 | 0x93 => {
                    let addr = val!(Int(
                        IntOp::Add,
                        B16,
                        val!(Int(
                            IntOp::Or,
                            B16,
                            val!(Int(
                                IntOp::Shl,
                                B16,
                                val!(Zext(B16, state.regs[Reg::DPH as usize])),
                                cx.a(Const::new(B8, 8))
                            )),
                            val!(Zext(B16, state.regs[Reg::DPL as usize]))
                        )),
                        val!(Zext(B16, state.regs[Reg::A as usize]))
                    ));
                    if op == 0x73 {
                        return jump!(addr);
                    } else {
                        // HACK(eddyb) lift MOVC only with statically known addresses,
                        // until proper support is added for Harvard architectures.
                        if let Some(addr) = cx[addr].as_const() {
                            state.regs[Reg::A as usize] =
                                cx.a(cx.platform.rom().load(addr, MemSize::M8).unwrap());
                        } else {
                            eprintln!(
                                "8051: unsupported dynamic MOVC address: {}",
                                cx.pretty_print(&addr)
                            );
                            // HACK(eddyb) this uses a B16 memory address to
                            // avoid accidentally aliasing B8 memory addresses.
                            state.regs[Reg::A as usize] = val!(Load(MemRef {
                                mem: state.mem,
                                addr,
                                size: MemSize::M8,
                            }));
                        }
                    }
                }
                0x80 => return jump!(relative_target!()),
                0x90 => {
                    state.regs[Reg::DPH as usize] = cx.a(imm!(8));
                    state.regs[Reg::DPL as usize] = cx.a(imm!(8));
                }
                0x92 => {
                    let bit = bit_addr!();
                    set!(val!(Int(
                        IntOp::Or,
                        B8,
                        get!(),
                        val!(Int(
                            IntOp::Shl,
                            B8,
                            val!(Zext(B8, state.regs[Reg::PSW_C as usize])),
                            cx.a(Const::new(B8, bit as u64))
                        ))
                    )));
                }
                0xb2 => {
                    let bit = bit_addr!();
                    set!(val!(Int(
                        IntOp::Xor,
                        B8,
                        get!(),
                        cx.a(Const::new(B8, 1 << bit))
                    )));
                }
                0xc0 => push!(get!(direct!())),
                0xc2 => {
                    let bit = bit_addr!();
                    set!(val!(Int(
                        IntOp::And,
                        B8,
                        get!(),
                        cx.a(Const::new(B8, (!(1u8 << bit)) as u64))
                    )));
                }
                0xd0 => set!(direct!(), pop!(M8)),
                0xd2 => {
                    let bit = bit_addr!();
                    set!(val!(Int(
                        IntOp::Or,
                        B8,
                        get!(),
                        cx.a(Const::new(B8, 1 << bit))
                    )));
                }
                _ => eprintln!("8051: unsupported opcode 0x{:x}", op),
            }
        }

        Ok(state)
    }
}

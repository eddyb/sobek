// TODO(eddyb) use a better name for this module.

use crate::ir::{
    BitSize::{self, *},
    Const, Cx, Edge, Edges, Effect, IntOp, Isa, Mem, MemRef, MemSize, Platform, Rom, State, Use,
    Val,
};
use std::iter;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Flavor {
    Intel,
    LR35902,
}

pub struct _8080 {
    pub flavor: Flavor,
}

// FIXME(eddyb) maybe replace `Reg` with enums like these.
pub enum Reg {
    A,
    F,
    B,
    C,
    D,
    E,
    H,
    L,
    SP,

    #[allow(non_camel_case_types)]
    F_C,
}

impl Isa for _8080 {
    const ADDR_SIZE: BitSize = B16;

    fn default_regs(cx: &mut Cx<impl Platform<Isa = Self>>) -> Vec<Use<Val>> {
        ["a", "f", "b", "c", "d", "e", "h", "l"]
            .iter()
            .enumerate()
            .map(|(i, name)| crate::ir::Reg {
                index: i,
                size: B8,
                name,
            })
            .chain(iter::once(crate::ir::Reg {
                index: Reg::SP as usize,
                size: B16,
                name: "sp",
            }))
            .chain(iter::once(crate::ir::Reg {
                index: Reg::F_C as usize,
                size: B1,
                name: "f.c",
            }))
            .map(|reg| cx.a(Val::InReg(reg)))
            .collect()
    }

    fn lift_instr(
        cx: &mut Cx<impl Platform<Isa = Self>>,
        pc: &mut Const,
        mut state: State,
    ) -> Result<State, Edges<Edge>> {
        let flavor = cx.platform.isa().flavor;

        let add1 = |x| IntOp::Add.eval(x, Const::new(x.size, 1)).unwrap();

        macro_rules! imm {
            (8) => {{
                let v = match cx.platform.rom().load(*pc, MemSize::M8) {
                    Ok(v) => v,
                    Err(e) => {
                        eprintln!("8080: failed to read ROM, emitting `Trap(0)`: {:?}", e);
                        return Err(Edges::One(Edge {
                            state,
                            effect: Effect::Trap { code: 0 },
                        }));
                    }
                };
                *pc = add1(*pc);
                v
            }};
            (16) => {
                Const::new(B16, imm!(8).as_u64() | (imm!(8).as_u64() << 8))
            };
        }

        let op = imm!(8).as_u8();

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
        macro_rules! mem_ref {
            ($addr:expr, $sz:ident) => {{
                let addr = $addr;
                assert_eq!(cx[addr].size(), B16);
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
                let sp = val!(int_sub(
                    state.regs[Reg::SP as usize],
                    cx.a(Const::new(B16, (size.bits() / 8) as u64))
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
                state.regs[Reg::SP as usize] = val!(Int(
                    IntOp::Add,
                    B16,
                    sp,
                    cx.a(Const::new(B16, (MemSize::$sz.bits() / 8) as u64))
                ));
                value
            }};
        }

        macro_rules! jump {
            ($target:expr) => {
                return Err(Edges::One(Edge {
                    effect: Effect::Jump($target),
                    state,
                }));
            };
        }
        macro_rules! relative_target {
            () => {{
                // FIXME(eddyb) impl `From<iN>` for `Const` already!
                let offset = Const::new(B16, imm!(8).as_i8() as i16 as u16 as u64);
                cx.a(IntOp::Add.eval(*pc, offset).unwrap())
            }};
        }
        macro_rules! condition_code {
            () => {
                // TODO(eddyb) actually implement this.
                cx.a(Const::new(B1, 0))
            };
        }
        // NOTE(eddyb) the expression inside `conditional!(...)`
        // *only* affects the state if the conditional is met
        // (i.e. on the "true" branch of the `Edges<Edge>`).
        macro_rules! conditional {
            ($effect:expr) => {{
                let cond = condition_code!();
                let e_state = state.clone();
                let t = Edge {
                    effect: $effect,
                    state,
                };
                let e = Edge {
                    state: e_state,
                    effect: Effect::Jump(cx.a(*pc)),
                };

                assert_eq!(cx[cond].size(), B1);

                return Err(Edges::Branch { cond, t, e });
            }};
        }

        let reserved = op == 0xdd
            || op == 0xed
            || op == 0xfd
            || match flavor {
                Flavor::Intel => (op & 0xc7) == 0 && op != 0 || op == 0xd9 || op == 0xcb,
                Flavor::LR35902 => {
                    (op & 0xf7) == 0xd3
                        || (op & 0xf7) == 0xe3
                        || (op & 0xf7) == 0xe4
                        || (op & 0xf7) == 0xf4
                }
            };
        if reserved {
            eprintln!("8080: reserved opcode, emitting `Trap(1)`: 0x{:x}", op);
            return Err(Edges::One(Edge {
                state,
                effect: Effect::Trap { code: 1 },
            }));
        }

        enum Operand {
            Reg(usize),
            Mem,
        }
        impl Operand {
            fn decode(i: u8) -> Self {
                match i {
                    0..=5 => Operand::Reg(Reg::B as usize + i as usize),
                    6 => Operand::Mem,
                    7 => Operand::Reg(Reg::A as usize),
                    _ => unreachable!(),
                }
            }
        }

        let mut dst = Operand::decode((op >> 3) & 7);
        let mut src = Operand::decode(op & 7);

        macro_rules! hl {
            () => {
                val!(Int(
                    IntOp::Or,
                    B16,
                    val!(Int(
                        IntOp::Shl,
                        B16,
                        val!(Zext(B16, state.regs[Reg::H as usize])),
                        cx.a(Const::new(B8, 8))
                    )),
                    val!(Zext(B16, state.regs[Reg::L as usize]))
                ))
            };
        }
        macro_rules! get {
            ($operand:expr) => {
                match $operand {
                    Operand::Reg(i) => state.regs[i],
                    Operand::Mem => val!(Load(mem_ref!(hl!(), M8))),
                }
            };
            () => {
                get!(src)
            };
        }
        macro_rules! set {
            ($operand:expr, $val:expr) => {{
                let val = $val;
                match $operand {
                    Operand::Reg(i) => state.regs[i] = val,
                    Operand::Mem => state.mem = mem!(Store(mem_ref!(hl!(), M8), val)),
                }
            }};
            ($val:expr) => {
                set!(dst, $val)
            };
        }

        // FIXME(eddyb) clean up these hacks.
        macro_rules! get_src {
            () => {
                if (op & 0xc7) == 0x06 || (op & 0xc7) == 0xc6 {
                    cx.a(imm!(8))
                } else {
                    get!()
                }
            };
        }

        if flavor == Flavor::LR35902 {
            match op {
                0x18 => jump!(relative_target!()),
                _ if (op & 0xe7) == 0x20 => {
                    // FIXME(eddyb) fix the condition code decoding,
                    // once implemented, to match these up correctly.
                    conditional!(Effect::Jump(relative_target!()));
                }
                _ if (op & 0xed) == 0xe0 => {
                    let m = mem_ref!(
                        val!(Int(
                            IntOp::Add,
                            B16,
                            cx.a(Const::new(B16, 0xff00)),
                            if (op & 2) == 0 {
                                cx.a(Const::new(B16, imm!(8).as_u64()))
                            } else {
                                val!(Zext(B16, state.regs[Reg::C as usize]))
                            }
                        )),
                        M8
                    );
                    if (op & 0xf0) == 0xe0 {
                        state.mem = mem!(Store(m, state.regs[Reg::A as usize]));
                    } else {
                        state.regs[Reg::A as usize] = val!(Load(m));
                    }
                    return Ok(state);
                }
                0xcb => {
                    let sub_op = imm!(8).as_u8();
                    dst = Operand::decode(sub_op & 7);
                    src = Operand::decode(sub_op & 7);
                    match sub_op & 0xf8 {
                        0x30 => set!(val!(bit_rol(get!(), cx.a(Const::new(B8, 4))))),
                        _ => eprintln!("8080: unsupported LR35902 CB sub-opcode 0x{:x}", sub_op),
                    }
                    return Ok(state);
                }
                0x10 | 0xe8 | 0xf8 => {
                    imm!(8);

                    eprintln!("8080: unsupported LR35902 opcode 0x{:x}", op);
                    return Ok(state);
                }
                0x08 | 0xea | 0xfa => {
                    imm!(16);

                    eprintln!("8080: unsupported LR35902 opcode 0x{:x}", op);
                    return Ok(state);
                }
                0x22 | 0x32 | 0x2a | 0x3a => {
                    eprintln!("8080: unsupported LR35902 opcode 0x{:x}", op);
                    return Ok(state);
                }
                _ => {}
            }
        }

        match op {
            _ if (op & 0xcf) == 0x01 => {
                let i = Reg::B as usize + (op >> 4) as usize * 2;
                if i == Reg::SP as usize {
                    state.regs[i] = cx.a(imm!(16));
                } else {
                    state.regs[i + 1] = cx.a(imm!(8));
                    state.regs[i] = cx.a(imm!(8));
                }
            }
            _ if (op & 0xc7) == 0x03 => {
                let i = Reg::B as usize + (op >> 4) as usize * 2;
                let mut val = if i == Reg::SP as usize {
                    state.regs[i]
                } else {
                    val!(Int(
                        IntOp::Or,
                        B16,
                        val!(Int(
                            IntOp::Shl,
                            B16,
                            val!(Zext(B16, state.regs[i])),
                            cx.a(Const::new(B8, 8))
                        )),
                        val!(Zext(B16, state.regs[i + 1]))
                    ))
                };
                val = if (op & 0x08) == 0 {
                    val!(Int(IntOp::Add, B16, val, cx.a(Const::new(B16, 1))))
                } else {
                    val!(int_sub(val, cx.a(Const::new(B16, 1))))
                };
                if i == Reg::SP as usize {
                    state.regs[i] = val;
                } else {
                    state.regs[i + 1] = val!(Trunc(B8, val));
                    state.regs[i] = val!(Trunc(
                        B8,
                        val!(Int(IntOp::ShrU, B16, val, cx.a(Const::new(B8, 8))))
                    ));
                }
            }
            _ if (op & 0xc0) == 0x40 || (op & 0xc7) == 0x06 => {
                set!(get_src!());
            }
            _ if (op & 0xc7) == 4 => {
                set!(val!(Int(
                    IntOp::Add,
                    B8,
                    get!(dst),
                    cx.a(Const::new(B8, 1))
                )));
            }
            _ if (op & 0xc7) == 5 => {
                set!(val!(int_sub(get!(dst), cx.a(Const::new(B8, 1)))));
            }
            _ if (op & 0xc0) == 0x80 || (op & 0xc7) == 0xc6 => {
                let operand = get_src!();
                state.regs[Reg::A as usize] = match op & 0xb8 {
                    0x80 => {
                        val!(Int(IntOp::Add, B8, state.regs[Reg::A as usize], operand))
                        // FIXME(eddyb) set the flags.
                    }
                    0x88 => {
                        val!(Int(
                            IntOp::Add,
                            B8,
                            val!(Int(IntOp::Add, B8, state.regs[Reg::A as usize], operand)),
                            val!(Zext(B8, state.regs[Reg::F_C as usize]))
                        ))
                        // FIXME(eddyb) set the flags.
                    }
                    0x90 => {
                        val!(int_sub(state.regs[Reg::A as usize], operand))
                        // FIXME(eddyb) set the flags.
                    }
                    0x98 => {
                        val!(int_sub(
                            val!(int_sub(state.regs[Reg::A as usize], operand)),
                            val!(Zext(B8, state.regs[Reg::F_C as usize]))
                        ))
                        // FIXME(eddyb) set the flags.
                    }
                    0xa0 => val!(Int(IntOp::And, B8, state.regs[Reg::A as usize], operand)),
                    0xa8 => val!(Int(IntOp::Xor, B8, state.regs[Reg::A as usize], operand)),
                    0xb0 => val!(Int(IntOp::Or, B8, state.regs[Reg::A as usize], operand)),
                    0xb8 => {
                        // TODO(eddyb) figure out the subtraction direction.
                        val!(int_sub(operand, state.regs[Reg::A as usize]));
                        // FIXME(eddyb) set the flags.
                        return Ok(state);
                    }
                    _ => unreachable!(),
                };
            }
            _ if (op & 0xc7) == 0xc2 => {
                conditional!(Effect::Jump(cx.a(imm!(16))));
            }
            _ if (op & 0xc7) == 0xc0 => {
                conditional!(Effect::Jump(pop!(M16)));
            }
            _ if (op & 0xc7) == 0xc4 => {
                conditional!({
                    let target = cx.a(imm!(16));
                    push!(cx.a(*pc));
                    Effect::Jump(target)
                });
            }

            0x00 => {}
            0x32 => {
                state.mem = mem!(Store(mem_ref!(cx.a(imm!(16))), state.regs[Reg::A as usize]));
            }
            0x3a => {
                state.regs[Reg::A as usize] = val!(Load(mem_ref!(cx.a(imm!(16)))));
            }
            0xc3 => jump!(cx.a(imm!(16))),
            0xc9 => jump!(pop!(M16)),
            0xcd => {
                let target = cx.a(imm!(16));
                push!(cx.a(*pc));
                jump!(target);
            }
            0xe9 => jump!(hl!()),

            0xd3 | 0xd8 | 0x22 | 0x2a => {
                assert_eq!(flavor, Flavor::Intel);
                panic!("8080: unsupporteed opcode 0x{:x} requires immediate", op);
            }

            _ => eprintln!("8080: unsupported opcode 0x{:x}", op),
        }

        Ok(state)
    }
}

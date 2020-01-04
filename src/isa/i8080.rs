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

pub struct I8080 {
    pub flavor: Flavor,
}

// FIXME(eddyb) maybe replace `Reg` with enums like these.
#[allow(non_camel_case_types)]
#[derive(Copy, Clone)]
pub enum Reg {
    A,

    BC,
    DE,
    HL,

    SP,

    // Flag bits.
    F_C,
    F_H, // AC on i8080, H on LR35902.
    F_N, // Missing on i8080, N on LR35902.
    F_Z,
    F_S, // S on i8080, missing on LR35902.
    F_P, // P on i8080, missing on LR35902.

    IE, // Interrupt Enable.
}

impl Flavor {
    fn flags(self) -> [Result<Reg, u8>; 8] {
        use self::Reg::*;
        match self {
            Flavor::Intel => [
                Ok(F_C),
                Err(1),
                Ok(F_P),
                Err(0),
                Ok(F_H),
                Err(0),
                Ok(F_Z),
                Ok(F_S),
            ],
            Flavor::LR35902 => [
                Err(0),
                Err(0),
                Err(0),
                Err(0),
                Ok(F_C),
                Ok(F_H),
                Ok(F_N),
                Ok(F_Z),
            ],
        }
    }
}

impl Isa for I8080 {
    const ADDR_SIZE: BitSize = B16;

    fn default_regs(cx: &Cx<impl Platform<Isa = Self>>) -> Vec<Use<Val>> {
        iter::once(crate::ir::Reg {
            index: Reg::A as usize,
            size: B8,
            name: "a",
        })
        .chain(
            ["bc", "de", "hl", "sp"]
                .iter()
                .enumerate()
                .map(|(i, name)| crate::ir::Reg {
                    index: Reg::BC as usize + i,
                    size: B16,
                    name,
                }),
        )
        .chain(
            // FIXME(eddyb) perhaps change names or even use different
            // sets of flags, depending on flavor.
            ["f.c", "f.h", "f.n", "f.z", "f.s", "f.p"]
                .iter()
                .enumerate()
                .map(|(i, name)| crate::ir::Reg {
                    index: Reg::F_C as usize + i,
                    size: B1,
                    name,
                }),
        )
        .chain(iter::once(crate::ir::Reg {
            index: Reg::IE as usize,
            size: B1,
            name: "ie",
        }))
        .map(|reg| cx.a(Val::InReg(reg)))
        .collect()
    }

    fn lift_instr(
        cx: &Cx<impl Platform<Isa = Self>>,
        pc: &mut Const,
        mut state: State,
    ) -> Result<State, Edges<Edge>> {
        let flavor = cx.platform.isa().flavor;

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
                let v = match cx.platform.rom().load(*pc, MemSize::M8) {
                    Ok(v) => v,
                    Err(e) => error!("failed to read ROM: {:?}", e),
                };
                *pc = add1(*pc);
                v
            }};
            (16) => {
                Const::new(B16, imm!(8).as_u64() | (imm!(8).as_u64() << 8))
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
                Err(Edges::One(Edge {
                    effect: Effect::Jump($target),
                    state,
                }))
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

                Err(Edges::Branch { cond, t, e })
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
            error!("reserved opcode: 0x{:x}", op);
        }

        enum Operand {
            RegA,
            RegLo(Reg),
            RegHi(Reg),
            Mem,
        }
        impl Operand {
            fn decode(i: u8) -> Self {
                match i {
                    0 => Operand::RegHi(Reg::BC),
                    1 => Operand::RegLo(Reg::BC),
                    2 => Operand::RegHi(Reg::DE),
                    3 => Operand::RegLo(Reg::DE),
                    4 => Operand::RegHi(Reg::HL),
                    5 => Operand::RegLo(Reg::HL),
                    6 => Operand::Mem,
                    7 => Operand::RegA,
                    _ => unreachable!(),
                }
            }
        }

        let mut dst = Operand::decode((op >> 3) & 7);
        let mut src = Operand::decode(op & 7);

        // FIXME(eddyb) move these macros into methods on helper types.
        macro_rules! get {
            ($operand:expr) => {
                match $operand {
                    Operand::RegA => state.regs[Reg::A as usize],
                    Operand::RegLo(r) => val!(Trunc(B8, state.regs[r as usize])),
                    Operand::RegHi(r) => val!(Trunc(
                        B8,
                        val!(Int(
                            IntOp::ShrU,
                            B16,
                            state.regs[r as usize],
                            cx.a(Const::new(B8, 8))
                        ))
                    )),
                    Operand::Mem => val!(Load(mem_ref!(state.regs[Reg::HL as usize]))),
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
                    Operand::RegA => state.regs[Reg::A as usize] = val,
                    Operand::RegLo(r) => {
                        state.regs[r as usize] = val!(Int(
                            IntOp::Or,
                            B16,
                            val!(Int(
                                IntOp::And,
                                B16,
                                state.regs[r as usize],
                                cx.a(Const::new(B16, 0xff00))
                            )),
                            val!(Zext(B16, val))
                        ))
                    }
                    Operand::RegHi(r) => {
                        state.regs[r as usize] = val!(Int(
                            IntOp::Or,
                            B16,
                            val!(Int(
                                IntOp::And,
                                B16,
                                state.regs[r as usize],
                                cx.a(Const::new(B16, 0x00ff))
                            )),
                            val!(Int(
                                IntOp::Shl,
                                B16,
                                val!(Zext(B16, val)),
                                cx.a(Const::new(B8, 8))
                            ))
                        ))
                    }
                    Operand::Mem => {
                        state.mem = mem!(Store(mem_ref!(state.regs[Reg::HL as usize]), val))
                    }
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
                0x08 => {
                    let m = mem_ref!(cx.a(imm!(16)), M16);
                    state.mem = mem!(Store(m, state.regs[Reg::SP as usize]));
                    return Ok(state);
                }
                0x18 => return jump!(relative_target!()),
                _ if (op & 0xe7) == 0x20 => {
                    // FIXME(eddyb) fix the condition code decoding,
                    // once implemented, to match these up correctly.
                    return conditional!(Effect::Jump(relative_target!()));
                }
                _ if (op & 0xe7) == 0x22 => {
                    if (op & 0x0f) == 0x02 {
                        set!(Operand::Mem, state.regs[Reg::A as usize]);
                    } else {
                        state.regs[Reg::A as usize] = get!(Operand::Mem);
                    }
                    let hl = state.regs[Reg::HL as usize];
                    let hl = if (op & 0xf0) == 0x20 {
                        val!(Int(IntOp::Add, B16, hl, cx.a(Const::new(B16, 1))))
                    } else {
                        val!(int_sub(hl, cx.a(Const::new(B16, 1))))
                    };
                    state.regs[Reg::HL as usize] = hl;
                    return Ok(state);
                }
                _ if (op & 0xed) == 0xe0 || (op & 0xef) == 0xea => {
                    let addr = if (op & 0x0f) == 0x0a {
                        cx.a(imm!(16))
                    } else {
                        val!(Int(
                            IntOp::Add,
                            B16,
                            cx.a(Const::new(B16, 0xff00)),
                            if (op & 2) == 0 {
                                cx.a(Const::new(B16, imm!(8).as_u64()))
                            } else {
                                val!(Zext(B16, get!(Operand::RegLo(Reg::BC))))
                            }
                        ))
                    };
                    let m = mem_ref!(addr);
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

                    // NB: only used by 0x40..=0xFF (BIT, RES, SET).
                    let bit_mask: u8 = 1 << ((sub_op >> 3) & 7);

                    let val = get!();
                    let val = match sub_op & 0xf8 {
                        0x00 => {
                            val!(bit_rol(val, cx.a(Const::new(B8, 1))))
                            // FIXME(eddyb) set the flags.
                        }
                        0x08 => {
                            val!(bit_ror(val, cx.a(Const::new(B8, 1))))
                            // FIXME(eddyb) set the flags.
                        }
                        0x10 => {
                            val!(bit_rol(val, cx.a(Const::new(B8, 1))))
                            // FIXME(eddyb) set (and read) the flags.
                        }
                        0x18 => {
                            val!(bit_ror(val, cx.a(Const::new(B8, 1))))
                            // FIXME(eddyb) set (and read) the flags.
                        }
                        0x20 => {
                            val!(Int(IntOp::Shl, B8, val, cx.a(Const::new(B8, 1))))
                            // FIXME(eddyb) set the flags.
                        }
                        0x28 => {
                            val!(Int(IntOp::ShrS, B8, val, cx.a(Const::new(B8, 1))))
                            // FIXME(eddyb) set the flags.
                        }
                        0x30 => {
                            val!(bit_rol(val, cx.a(Const::new(B8, 4))))
                            // FIXME(eddyb) set the flags.
                        }
                        0x38 => {
                            val!(Int(IntOp::ShrU, B8, val, cx.a(Const::new(B8, 1))))
                            // FIXME(eddyb) set the flags.
                        }
                        0x40..=0x78 => {
                            state.regs[Reg::F_Z as usize] = val!(Int(
                                IntOp::Eq,
                                B8,
                                val!(Int(
                                    IntOp::And,
                                    B8,
                                    val,
                                    cx.a(Const::new(B8, bit_mask as u64))
                                )),
                                cx.a(Const::new(B8, 0))
                            ));
                            state.regs[Reg::F_N as usize] = cx.a(Const::new(B1, 0));
                            state.regs[Reg::F_H as usize] = cx.a(Const::new(B1, 1));

                            return Ok(state);
                        }
                        0x80..=0xb8 => val!(Int(
                            IntOp::And,
                            B8,
                            val,
                            cx.a(Const::new(B8, !bit_mask as u64))
                        )),
                        0xc0..=0xf8 => val!(Int(
                            IntOp::Or,
                            B8,
                            val,
                            cx.a(Const::new(B8, bit_mask as u64))
                        )),
                        _ => unreachable!(),
                    };
                    set!(val);
                    return Ok(state);
                }
                0xd9 => {
                    state.regs[Reg::IE as usize] = cx.a(Const::new(B1, 1));
                    return jump!(pop!(M16));
                }
                0x10 | 0xe8 | 0xf8 => {
                    imm!(8);

                    error!("unsupported LR35902 opcode 0x{:x}", op);
                }
                _ => {}
            }
        }

        match op {
            _ if (op & 0xc5) == 0x01 => {
                let mut i = Reg::BC as usize + (op >> 4) as usize;
                let mut val = state.regs[i];
                val = match op & 0x0f {
                    0x01 => cx.a(imm!(16)),
                    0x03 => val!(Int(IntOp::Add, B16, val, cx.a(Const::new(B16, 1)))),
                    0x09 => {
                        // HACK(eddyb) this allows reusing the rest of the code.
                        i = Reg::HL as usize;

                        val!(Int(IntOp::Add, B16, state.regs[Reg::HL as usize], val))
                    }
                    0x0b => val!(int_sub(val, cx.a(Const::new(B16, 1)))),
                    _ => unreachable!(),
                };
                state.regs[i] = val;
            }
            _ if (op & 0xe7) == 0x02 => {
                let addr = state.regs[Reg::BC as usize + (op >> 4) as usize];
                let m = mem_ref!(addr);
                if (op & 0x0f) == 0x02 {
                    state.mem = mem!(Store(m, state.regs[Reg::A as usize]));
                } else {
                    state.regs[Reg::A as usize] = val!(Load(m));
                }
                return Ok(state);
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
            _ if (op & 0xc7) == 0xc0 => {
                return conditional!(Effect::Jump(pop!(M16)));
            }
            // HACK(eddyb) `push AF` / `pop AF` are special-cased because `AF`
            // is not a register (like `BC`/`DE`/`HL` are), as this is the only
            // place where flags are encoded/decoded into/from a byte.
            0xf1 => {
                let flags = pop!(M8);
                for (i, &flag) in flavor.flags().iter().enumerate() {
                    if let Ok(reg) = flag {
                        state.regs[reg as usize] = val!(Trunc(
                            B1,
                            val!(Int(IntOp::ShrU, B8, flags, cx.a(Const::new(B8, i as u64))))
                        ));
                    }
                }

                state.regs[Reg::A as usize] = pop!(M8);
            }
            0xf5 => {
                push!(state.regs[Reg::A as usize]);

                push!(flavor
                    .flags()
                    .iter()
                    .map(|&flag| {
                        match flag {
                            Ok(reg) => state.regs[reg as usize],
                            Err(c) => cx.a(Const::new(B1, c as u64)),
                        }
                    })
                    .enumerate()
                    .map(|(i, bit)| {
                        val!(Int(
                            IntOp::Shl,
                            B8,
                            val!(Zext(B8, bit)),
                            cx.a(Const::new(B8, i as u64))
                        ))
                    })
                    .fold(cx.a(Const::new(B8, 0)), |a, b| val!(Int(
                        IntOp::Or,
                        B8,
                        a,
                        b
                    ))));
            }
            _ if (op & 0xcb) == 0xc1 => {
                let i = (op >> 4) & 0x3;
                let i = Reg::BC as usize + (i as usize);
                if (op & 4) == 0 {
                    state.regs[i] = pop!(M16);
                } else {
                    push!(state.regs[i]);
                }
            }
            _ if (op & 0xc7) == 0xc2 => {
                return conditional!(Effect::Jump(cx.a(imm!(16))));
            }
            _ if (op & 0xc7) == 0xc4 => {
                return conditional!({
                    let target = cx.a(imm!(16));
                    push!(cx.a(*pc));
                    Effect::Jump(target)
                });
            }
            _ if (op & 0xc7) == 0xc7 => {
                let i = (op >> 3) & 7;
                push!(cx.a(*pc));
                return jump!(cx.a(Const::new(B16, ((i as u16) * 8) as u64)));
            }
            _ if op & 0xf7 == 0xf3 => {
                state.regs[Reg::IE as usize] = cx.a(Const::new(B1, ((op >> 3) & 1) as u64));
            }

            0x00 => {}
            0x07 => {
                state.regs[Reg::A as usize] = val!(bit_rol(
                    state.regs[Reg::A as usize],
                    cx.a(Const::new(B8, 1))
                ));
                // FIXME(eddyb) set the flags.
            }
            0x27 => {
                // FIXME(eddyb) actually implement.
            }
            0x2f => {
                state.regs[Reg::A as usize] = val!(bit_not(state.regs[Reg::A as usize]));
            }
            0x32 => {
                state.mem = mem!(Store(mem_ref!(cx.a(imm!(16))), state.regs[Reg::A as usize]));
            }
            0x3a => {
                state.regs[Reg::A as usize] = val!(Load(mem_ref!(cx.a(imm!(16)))));
            }
            0xc3 => return jump!(cx.a(imm!(16))),
            0xc9 => return jump!(pop!(M16)),
            0xcd => {
                let target = cx.a(imm!(16));
                push!(cx.a(*pc));
                return jump!(target);
            }
            0xe9 => return jump!(state.regs[Reg::HL as usize]),
            0xeb => {
                state.regs.swap(Reg::DE as usize, Reg::HL as usize);
            }

            0xd3 | 0xd8 | 0x22 | 0x2a => {
                assert_eq!(flavor, Flavor::Intel);
                error!("unsupported opcode 0x{:x} requires immediate", op);
            }

            _ => error!("unsupported opcode 0x{:x}", op),
        }

        Ok(state)
    }
}

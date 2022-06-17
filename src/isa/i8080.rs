use crate::ir::{
    BitSize::*, Const, Cx, Edge, Edges, Effect, Global, IGlobal, MemRef, MemSize, MemType, State,
    Type,
};
use crate::isa::Isa;
use crate::platform::Rom;
use std::ops::Index;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Flavor {
    Intel,
    LR35902,
}

pub struct I8080 {
    flavor: Flavor,
    mem: IGlobal,
    regs: Regs,
}

impl I8080 {
    const MEM_TYPE: MemType = MemType {
        addr_size: B16,
        big_endian: false,
    };

    pub fn new(cx: &Cx) -> Self {
        I8080 {
            flavor: Flavor::Intel,
            mem: cx.a(Global {
                ty: Type::Mem(Self::MEM_TYPE),
                name: cx.a("m"),
            }),
            regs: Regs::new(cx),
        }
    }

    pub fn new_lr35902(cx: &Cx) -> Self {
        I8080 {
            flavor: Flavor::LR35902,
            mem: cx.a(Global {
                ty: Type::Mem(Self::MEM_TYPE),
                name: cx.a("m"),
            }),
            regs: Regs::new(cx),
        }
    }
}

struct Regs {
    a: IGlobal,

    reg16: [IGlobal; 4],

    // Flag bits.
    f_c: IGlobal,
    f_h: IGlobal, // AC on i8080, H on LR35902.
    f_n: IGlobal, // Missing on i8080, N on LR35902.
    f_z: IGlobal,
    f_s: IGlobal, // S on i8080, missing on LR35902.
    f_p: IGlobal, // P on i8080, missing on LR35902.

    ie: IGlobal, // Interrupt Enable.
}

impl Regs {
    fn new(cx: &Cx) -> Self {
        let reg = |size, name| {
            cx.a(Global {
                ty: Type::Bits(size),
                name: cx.a(name),
            })
        };

        Regs {
            a: reg(B8, "a"),

            reg16: [
                reg(B16, "bc"),
                reg(B16, "de"),
                reg(B16, "hl"),
                reg(B16, "sp"),
            ],

            // FIXME(eddyb) perhaps change names or even use different
            // sets of flags, depending on flavor.
            // FIXME(eddyb) avoid the repetition here (between field and name).
            f_c: reg(B1, "f.c"),
            f_h: reg(B1, "f.h"),
            f_n: reg(B1, "f.n"),
            f_z: reg(B1, "f.z"),
            f_s: reg(B1, "f.s"),
            f_p: reg(B1, "f.p"),

            ie: reg(B1, "ie"),
        }
    }
}

#[derive(Copy, Clone)]
pub enum Reg16 {
    BC,
    DE,
    HL,

    SP,
}

impl Index<Reg16> for Regs {
    type Output = IGlobal;

    fn index(&self, r: Reg16) -> &IGlobal {
        &self.reg16[r as usize]
    }
}

impl I8080 {
    fn flags(&self) -> [Result<IGlobal, u8>; 8] {
        let Regs {
            f_c,
            f_h,
            f_n,
            f_z,
            f_s,
            f_p,
            ..
        } = self.regs;

        match self.flavor {
            Flavor::Intel => [
                Ok(f_c),
                Err(1),
                Ok(f_p),
                Err(0),
                Ok(f_h),
                Err(0),
                Ok(f_z),
                Ok(f_s),
            ],
            Flavor::LR35902 => [
                Err(0),
                Err(0),
                Err(0),
                Err(0),
                Ok(f_c),
                Ok(f_h),
                Ok(f_n),
                Ok(f_z),
            ],
        }
    }
}

impl Isa for I8080 {
    fn mem_containing_rom(&self) -> IGlobal {
        self.mem
    }

    fn lift_instr(
        &self,
        cx: &Cx,
        rom: &dyn Rom,
        pc: &mut Const,
        mut state: State,
    ) -> Result<State, Edges<Edge>> {
        let flavor = self.flavor;

        // FIXME(eddyb) make it possible to write this as `x + 1`.
        let add1 = |x: Const| x + Const::new(x.size, 1);

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
                let v = match rom.load(Self::MEM_TYPE, *pc, MemSize::M8) {
                    Ok(v) => v,
                    Err(e) => error!("failed to read ROM: {:?}", e),
                };
                *pc = add1(*pc);
                v
            }};
            (16) => {
                imm!(8).zext(B16) | (imm!(8).zext(B16) << 8)
            };
        }

        let op = imm!(8).as_u8();

        macro_rules! mem_ref {
            ($addr:expr, $sz:ident) => {
                MemRef {
                    mem: state.get(cx, self.mem),
                    mem_type: Self::MEM_TYPE,
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
                let sp = cx
                    .a(state.get(cx, self.regs[Reg16::SP])
                        - Const::new(B16, (size.bits() / 8) as u64));
                state.set(cx, self.regs[Reg16::SP], sp);
                let m = match size {
                    B8 => mem_ref!(sp),
                    B16 => mem_ref!(sp, M16),
                    _ => unreachable!(),
                };
                state.set(cx, self.mem, cx.a(m.store(value)));
            }};
        }

        macro_rules! pop {
            ($sz:ident) => {{
                let sp = state.get(cx, self.regs[Reg16::SP]);
                let value = cx.a(mem_ref!(sp, $sz).load());
                state.set(
                    cx,
                    self.regs[Reg16::SP],
                    cx.a(sp + Const::new(B16, MemSize::$sz.bytes() as u64)),
                );
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
                let offset = imm!(8).sext(B16);
                cx.a(*pc + offset)
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

                assert_eq!(cx[cond].ty(cx), Type::Bits(B1));

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
            RegLo(Reg16),
            RegHi(Reg16),
            Mem,
        }
        impl Operand {
            fn decode(i: u8) -> Self {
                match i {
                    0 => Operand::RegHi(Reg16::BC),
                    1 => Operand::RegLo(Reg16::BC),
                    2 => Operand::RegHi(Reg16::DE),
                    3 => Operand::RegLo(Reg16::DE),
                    4 => Operand::RegHi(Reg16::HL),
                    5 => Operand::RegLo(Reg16::HL),
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
                    Operand::RegA => state.get(cx, self.regs.a),
                    Operand::RegLo(r) => cx.a(state.get(cx, self.regs[r]).trunc(B8)),
                    Operand::RegHi(r) => cx.a(state.get(cx, self.regs[r]).shr_u(8).trunc(B8)),
                    Operand::Mem => cx.a(mem_ref!(state.get(cx, self.regs[Reg16::HL])).load()),
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
                    Operand::RegA => state.set(cx, self.regs.a, val),
                    Operand::RegLo(r) => state.set(
                        cx,
                        self.regs[r],
                        cx.a((state.get(cx, self.regs[r]) & Const::new(B16, 0xff00))
                            | (val.zext(B16))),
                    ),
                    Operand::RegHi(r) => state.set(
                        cx,
                        self.regs[r],
                        cx.a((state.get(cx, self.regs[r]) & Const::new(B16, 0x00ff))
                            | (val.zext(B16) << 8)),
                    ),
                    Operand::Mem => state.set(
                        cx,
                        self.mem,
                        cx.a(mem_ref!(state.get(cx, self.regs[Reg16::HL])).store(val)),
                    ),
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
                    let m = mem_ref!(imm!(16), M16);
                    state.set(
                        cx,
                        self.mem,
                        cx.a(m.store(state.get(cx, self.regs[Reg16::SP]))),
                    );
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
                        set!(Operand::Mem, state.get(cx, self.regs.a));
                    } else {
                        state.set(cx, self.regs.a, get!(Operand::Mem));
                    }
                    let hl = state.get(cx, self.regs[Reg16::HL]);
                    let hl = if (op & 0xf0) == 0x20 {
                        cx.a(hl + Const::new(B16, 1))
                    } else {
                        cx.a(hl - Const::new(B16, 1))
                    };
                    state.set(cx, self.regs[Reg16::HL], hl);
                    return Ok(state);
                }
                _ if (op & 0xed) == 0xe0 || (op & 0xef) == 0xea => {
                    let addr = if (op & 0x0f) == 0x0a {
                        cx.a(imm!(16))
                    } else {
                        cx.a(Const::new(B16, 0xff00)
                            + if (op & 2) == 0 {
                                cx.a(Const::new(B16, imm!(8).as_u64()))
                            } else {
                                cx.a(get!(Operand::RegLo(Reg16::BC)).zext(B16))
                            })
                    };
                    let m = mem_ref!(addr);
                    if (op & 0xf0) == 0xe0 {
                        state.set(cx, self.mem, cx.a(m.store(state.get(cx, self.regs.a))));
                    } else {
                        state.set(cx, self.regs.a, cx.a(m.load()));
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
                            cx.a(val.rol(1))
                            // FIXME(eddyb) set the flags.
                        }
                        0x08 => {
                            cx.a(val.ror(1))
                            // FIXME(eddyb) set the flags.
                        }
                        0x10 => {
                            cx.a(val.rol(1))
                            // FIXME(eddyb) set (and read) the flags.
                        }
                        0x18 => {
                            cx.a(val.ror(1))
                            // FIXME(eddyb) set (and read) the flags.
                        }
                        0x20 => {
                            cx.a(val << 1)
                            // FIXME(eddyb) set the flags.
                        }
                        0x28 => {
                            cx.a(val.shr_s(1))
                            // FIXME(eddyb) set the flags.
                        }
                        0x30 => {
                            cx.a(val.rol(4))
                            // FIXME(eddyb) set the flags.
                        }
                        0x38 => {
                            cx.a(val.shr_u(1))
                            // FIXME(eddyb) set the flags.
                        }
                        0x40..=0x78 => {
                            state.set(
                                cx,
                                self.regs.f_z,
                                cx.a((val & Const::new(B8, bit_mask as u64))
                                    .cmp_eq(Const::new(B8, 0))),
                            );
                            state.set(cx, self.regs.f_n, cx.a(Const::new(B1, 0)));
                            state.set(cx, self.regs.f_h, cx.a(Const::new(B1, 1)));

                            return Ok(state);
                        }
                        0x80..=0xb8 => cx.a(val & Const::new(B8, !bit_mask as u64)),
                        0xc0..=0xf8 => cx.a(val | Const::new(B8, bit_mask as u64)),
                        _ => unreachable!(),
                    };
                    set!(val);
                    return Ok(state);
                }
                0xd9 => {
                    state.set(cx, self.regs.ie, cx.a(Const::new(B1, 1)));
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
                let mut i = Reg16::BC as usize + (op >> 4) as usize;
                let mut val = state.get(cx, self.regs.reg16[i]);
                val = match op & 0x0f {
                    0x01 => cx.a(imm!(16)),
                    0x03 => cx.a(val + Const::new(B16, 1)),
                    0x09 => {
                        // HACK(eddyb) this allows reusing the rest of the code.
                        i = Reg16::HL as usize;

                        cx.a(state.get(cx, self.regs[Reg16::HL]) + val)
                    }
                    0x0b => cx.a(val - Const::new(B16, 1)),
                    _ => unreachable!(),
                };
                state.set(cx, self.regs.reg16[i], val);
            }
            _ if (op & 0xe7) == 0x02 => {
                let addr = state.get(cx, self.regs.reg16[Reg16::BC as usize + (op >> 4) as usize]);
                let m = mem_ref!(addr);
                if (op & 0x0f) == 0x02 {
                    state.set(cx, self.mem, cx.a(m.store(state.get(cx, self.regs.a))));
                } else {
                    state.set(cx, self.regs.a, cx.a(m.load()));
                }
                return Ok(state);
            }
            _ if (op & 0xc0) == 0x40 || (op & 0xc7) == 0x06 => {
                set!(get_src!());
            }
            _ if (op & 0xc7) == 4 => {
                set!(cx.a(get!(dst) + Const::new(B8, 1)));
            }
            _ if (op & 0xc7) == 5 => {
                set!(cx.a(get!(dst) - Const::new(B8, 1)));
            }
            _ if (op & 0xc0) == 0x80 || (op & 0xc7) == 0xc6 => {
                let operand = get_src!();
                state.set(
                    cx,
                    self.regs.a,
                    match op & 0xb8 {
                        0x80 => {
                            cx.a(state.get(cx, self.regs.a) + operand)
                            // FIXME(eddyb) set the flags.
                        }
                        0x88 => {
                            cx.a(state.get(cx, self.regs.a)
                                + operand
                                + state.get(cx, self.regs.f_c).zext(B8))
                            // FIXME(eddyb) set the flags.
                        }
                        0x90 => {
                            cx.a(state.get(cx, self.regs.a) - operand)
                            // FIXME(eddyb) set the flags.
                        }
                        0x98 => {
                            cx.a(state.get(cx, self.regs.a)
                                - operand
                                - state.get(cx, self.regs.f_c).zext(B8))
                            // FIXME(eddyb) set the flags.
                        }
                        0xa0 => cx.a(state.get(cx, self.regs.a) & operand),
                        0xa8 => cx.a(state.get(cx, self.regs.a) ^ operand),
                        0xb0 => cx.a(state.get(cx, self.regs.a) | operand),
                        0xb8 => {
                            // TODO(eddyb) figure out the subtraction direction.
                            cx.a(operand - state.get(cx, self.regs.a));
                            // FIXME(eddyb) set the flags.
                            return Ok(state);
                        }
                        _ => unreachable!(),
                    },
                );
            }
            _ if (op & 0xc7) == 0xc0 => {
                return conditional!(Effect::Jump(pop!(M16)));
            }
            // HACK(eddyb) `push AF` / `pop AF` are special-cased because `AF`
            // is not a register (like `BC`/`DE`/`HL` are), as this is the only
            // place where flags are encoded/decoded into/from a byte.
            0xf1 => {
                let flags = pop!(M8);
                for (i, &flag) in self.flags().iter().enumerate() {
                    if let Ok(reg) = flag {
                        state.set(cx, reg, cx.a(flags.shr_u(i as u32).trunc(B1)));
                    }
                }

                let a = pop!(M8);
                state.set(cx, self.regs.a, a);
            }
            0xf5 => {
                push!(state.get(cx, self.regs.a));

                push!(self
                    .flags()
                    .iter()
                    .map(|&flag| {
                        match flag {
                            Ok(reg) => state.get(cx, reg),
                            Err(c) => cx.a(Const::new(B1, c as u64)),
                        }
                    })
                    .enumerate()
                    .map(|(i, bit)| cx.a(bit.zext(B8) << (i as u32)))
                    .fold(cx.a(Const::new(B8, 0)), |a, b| cx.a(a | b)));
            }
            _ if (op & 0xcb) == 0xc1 => {
                let i = (op >> 4) & 0x3;
                let i = Reg16::BC as usize + (i as usize);
                if (op & 4) == 0 {
                    let v = pop!(M16);
                    state.set(cx, self.regs.reg16[i], v);
                } else {
                    push!(state.get(cx, self.regs.reg16[i]));
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
                state.set(
                    cx,
                    self.regs.ie,
                    cx.a(Const::new(B1, ((op >> 3) & 1) as u64)),
                );
            }

            0x00 => {}
            0x07 => {
                state.set(cx, self.regs.a, cx.a(state.get(cx, self.regs.a).rol(1)));
                // FIXME(eddyb) set the flags.
            }
            0x27 => {
                // FIXME(eddyb) actually implement.
            }
            0x2f => {
                state.set(cx, self.regs.a, cx.a(!state.get(cx, self.regs.a)));
            }
            0x32 => {
                state.set(
                    cx,
                    self.mem,
                    cx.a(mem_ref!(imm!(16)).store(state.get(cx, self.regs.a))),
                );
            }
            0x3a => {
                state.set(cx, self.regs.a, cx.a(mem_ref!(imm!(16)).load()));
            }
            0xc3 => return jump!(cx.a(imm!(16))),
            0xc9 => return jump!(pop!(M16)),
            0xcd => {
                let target = cx.a(imm!(16));
                push!(cx.a(*pc));
                return jump!(target);
            }
            0xe9 => return jump!(state.get(cx, self.regs[Reg16::HL])),
            0xeb => {
                let de = state.get(cx, self.regs[Reg16::DE]);
                let hl = state.get(cx, self.regs[Reg16::HL]);
                state.set(cx, self.regs[Reg16::DE], hl);
                state.set(cx, self.regs[Reg16::HL], de);
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

use crate::ir::{
    BitSize::{self, *},
    Const, Cx, Edge, Edges, Effect, Global, IGlobal, INode, IntOp, MemRef, MemSize, MemType, Node,
    State, Type,
};
use crate::isa::Isa;
use crate::platform::Rom;
use core::fmt;
use std::{convert::Infallible, num::NonZeroU8, ops::Index};

pub struct Mips {
    mem: IGlobal,
    mem_type: MemType,
    regs: Regs,
}

impl Mips {
    pub fn new_32le(cx: &Cx) -> Self {
        Self::new(cx, B32, false)
    }
    pub fn new_32be(cx: &Cx) -> Self {
        Self::new(cx, B32, true)
    }
    pub fn new_64le(cx: &Cx) -> Self {
        Self::new(cx, B64, false)
    }
    pub fn new_64be(cx: &Cx) -> Self {
        Self::new(cx, B64, true)
    }
    fn new(cx: &Cx, reg_size: BitSize, big_endian: bool) -> Self {
        let mem_type = MemType {
            addr_size: reg_size,
            big_endian,
        };
        Mips {
            mem: cx.a(Global {
                ty: Type::Mem(mem_type),
                name: cx.a("m"),
            }),
            mem_type,
            regs: Regs::new(cx, reg_size),
        }
    }
}

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

impl Mips {
    // FIXME(eddyb) extend this to 64-bit virtual addresses, and redefine the
    // 32-bit virtual address decoding as `decode64(sext_64(addr32))`.
    pub fn decode_virtual_addr32(addr: u32) -> (AddrSpace, u32) {
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

struct Regs {
    /// Cached register `BitSize`, to avoid looking it up in a register's type.
    size: BitSize,
    gpr_without_zero: [IGlobal; 31],
    lo: IGlobal,
    hi: IGlobal,
}

impl Regs {
    fn new(cx: &Cx, size: BitSize) -> Self {
        let reg = |name| {
            cx.a(Global {
                ty: Type::Bits(size),
                name: cx.a(name),
            })
        };

        macro_rules! reg_array {
            ($($name:ident)*) => {
                [$(reg(stringify!($name))),*]
            }
        }

        Regs {
            size,
            gpr_without_zero: reg_array![
                // `zero` register omitted.
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
            ],
            lo: reg("lo"),
            hi: reg("hi"),
        }
    }
}

#[derive(Copy, Clone)]
enum Reg {
    Gpr(NonZeroU8),
    Lo,
    Hi,
}

/// Error type for attempting to refer to the `zero` register through `Reg`.
struct ZeroReg;

impl From<Infallible> for ZeroReg {
    fn from(never: Infallible) -> Self {
        match never {}
    }
}

impl TryFrom<u32> for Reg {
    type Error = ZeroReg;
    fn try_from(i: u32) -> Result<Self, ZeroReg> {
        assert!(matches!(i, 0..=31));
        Ok(Reg::Gpr(NonZeroU8::new(i as u8).ok_or(ZeroReg)?))
    }
}

impl Index<Reg> for Regs {
    type Output = IGlobal;

    fn index(&self, r: Reg) -> &IGlobal {
        match r {
            Reg::Gpr(i) => &self.gpr_without_zero[i.get() as usize - 1],
            Reg::Lo => &self.lo,
            Reg::Hi => &self.hi,
        }
    }
}

/// Error type for attempting to use a 64-bit operation (presumably from MIPS64)
/// on MIPS32.
// FIXME(eddyb) actually check opcodes instead of just reacting to `B64` values.
#[derive(Debug)]
enum Mips64OpNotSupportedOnMips32<'a> {
    RegRead { name: &'a str },
    RegWrite { name: &'a str },
}

impl fmt::Display for Mips64OpNotSupportedOnMips32<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::RegRead { name } => write!(f, "64-bit read from `{}` on MIPS32", name),
            Self::RegWrite { name } => write!(f, "64-bit write to `{}` on MIPS32", name),
        }
    }
}

// FIXME(eddyb) make a `State` wrapper to contain these helpers.
impl State {
    fn mips_get_reg_with_explicit_size<'a>(
        &self,
        isa: &Mips,
        cx: &'a Cx,
        r: impl TryInto<Reg, Error = impl Into<ZeroReg>>,
        explicit_size: BitSize,
    ) -> Result<INode, Mips64OpNotSupportedOnMips32<'a>> {
        let r = r.try_into().map_err(|e| e.into());
        let v = match r {
            Ok(r) => self.get(cx, isa.regs[r]),
            Err(ZeroReg) => cx.a(Const::new(isa.regs.size, 0)),
        };
        let v = match (isa.regs.size, explicit_size) {
            (B32, B32) | (B64, B64) => v,
            (B64, B32) => {
                // 32-bit register read on MIPS64, likely ALU.
                // FIXME(eddyb) need to encode the fact that the 64-bit `v` must
                // be equal to `sext_64(trunc_32(v))`, or otherwise this is UB.
                cx.a(Node::Trunc(B32, v))
            }
            (B32, B64) => {
                return Err(Mips64OpNotSupportedOnMips32::RegRead {
                    name: match r {
                        Ok(r) => &cx[cx[isa.regs[r]].name],
                        Err(ZeroReg) => "zero",
                    },
                })
            }
            _ => unreachable!(),
        };
        Ok(v)
    }

    fn mips_set_reg_with_explicit_size<'a>(
        &mut self,
        isa: &Mips,
        cx: &'a Cx,
        r: impl TryInto<Reg, Error = impl Into<ZeroReg>>,
        v: INode,
        explicit_size: BitSize,
    ) -> Result<(), Mips64OpNotSupportedOnMips32<'a>> {
        assert_eq!(explicit_size, cx[v].ty(cx).bit_size().unwrap());

        let r = r.try_into().map_err(|e| e.into());
        let v = match (isa.regs.size, explicit_size) {
            (B32, B32) | (B64, B64) => v,
            (B64, B32) => {
                // 32-bit register write on MIPS64, likely ALU or (small) loads.
                cx.a(Node::Sext(B64, v))
            }
            (B32, B64) => {
                return Err(Mips64OpNotSupportedOnMips32::RegWrite {
                    name: match r {
                        Ok(r) => &cx[cx[isa.regs[r]].name],
                        Err(ZeroReg) => "zero",
                    },
                })
            }
            _ => unreachable!(),
        };
        match r {
            Ok(r) => self.set(cx, isa.regs[r], v),
            // Writes to the zero register are noops.
            Err(ZeroReg) => {}
        }
        Ok(())
    }
}

impl Isa for Mips {
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
        macro_rules! error {
            ($($args:tt)*) => {
                return Err(Edges::One(Edge {
                    state,
                    effect: Effect::Error(format!($($args)*)),
                }))
            }
        }

        let instr = match rom.load(self.mem_type, *pc, MemSize::M32) {
            Ok(x) => x,
            Err(e) => error!("failed to read ROM: {:?}", e),
        };
        let add4 = |x| IntOp::Add.eval(x, Const::new(x.size, 4)).unwrap();
        *pc = add4(*pc);

        let field = |i, w| (instr.as_u32() >> i) & ((1u32 << w) - 1u32);

        let op = field(26, 6);
        let (rs, rt, rd) = {
            let r = |i| field(11 + 5 * i, 5);
            (r(2), r(1), r(0))
        };
        let imm16 = instr.trunc(B16);

        macro_rules! node {
            ($name:ident($($arg:expr),*)) => {
                cx.a(Node::$name($($arg),*))
            }
        }

        // Read the full width of a register.
        macro_rules! get_reg_native {
            ($r:expr) => {
                state
                    .mips_get_reg_with_explicit_size(self, cx, $r, self.regs.size)
                    .expect("get_reg_native forces `regs.size`, instead of `alu_size`")
            };
        }
        // Write the width width of a register.
        macro_rules! set_reg_native {
            ($r:expr, $val:expr) => {
                state
                    .mips_set_reg_with_explicit_size(self, cx, $r, $val, self.regs.size)
                    .expect("set_reg_native forces `regs.size`, instead of `alu_size`")
            };
        }

        macro_rules! link {
            ($r:expr) => {
                set_reg_native!($r, cx.a(add4(*pc)))
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
                    .eval(
                        *pc,
                        Const::new(B32, (imm16.sext(B32).as_u32() << 2) as u64)
                            .sext(self.mem_type.addr_size),
                    )
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

        // FIXME(eddyb) audit everything that ever interacts with this.
        let mut alu_size = B32;
        macro_rules! get_reg_alu_input {
            ($r:expr) => {
                match state.mips_get_reg_with_explicit_size(self, cx, $r, alu_size) {
                    Ok(v) => v,
                    Err(e) => error!("attempted {}", e),
                }
            };
        }
        macro_rules! set_reg_alu_output {
            ($r:expr, $val:expr) => {
                match state.mips_set_reg_with_explicit_size(self, cx, $r, $val, alu_size) {
                    Ok(()) => {}
                    Err(e) => error!("attempted {}", e),
                }
            };
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

            if let 20..=23 | 28..=31 | 44..=47 | 56 | 58..=60 | 62 | 63 = funct {
                // HACK(eddyb) force `{get,set}_reg_alu_{input,output}` below into 64-bit mode.
                alu_size = B64;
            }

            if let 8 | 9 | 16..=19 | 36..=39 | 42 | 43 = funct {
                // HACK(eddyb) force `{get,set}_reg_alu_{input,output}` below into "native" mode.
                alu_size = self.regs.size;
            }

            let rs = get_reg_alu_input!(rs);
            let rt = get_reg_alu_input!(rt);
            let sa = field(6, 5);
            let v = match funct {
                0 | 56 => node!(Int(
                    IntOp::Shl,
                    alu_size,
                    rt,
                    cx.a(Const::new(B32, sa as u64))
                )),
                2 | 58 => node!(Int(
                    IntOp::ShrU,
                    alu_size,
                    rt,
                    cx.a(Const::new(B32, sa as u64))
                )),
                3 | 59 => node!(Int(
                    IntOp::ShrS,
                    alu_size,
                    rt,
                    cx.a(Const::new(B32, sa as u64))
                )),

                8 => return jump!(rs),
                9 => {
                    link!(rd);
                    return jump!(rs);
                }

                16 => get_reg_native!(Reg::Hi),
                17 => {
                    set_reg_native!(Reg::Hi, rs);
                    return Ok(state);
                }
                18 => get_reg_native!(Reg::Lo),
                19 => {
                    set_reg_native!(Reg::Lo, rs);
                    return Ok(state);
                }

                26 | 30 => {
                    set_reg_alu_output!(Reg::Lo, node!(Int(IntOp::DivS, alu_size, rs, rt)));
                    set_reg_alu_output!(Reg::Hi, node!(Int(IntOp::RemS, alu_size, rs, rt)));
                    return Ok(state);
                }

                27 | 31 => {
                    set_reg_alu_output!(Reg::Lo, node!(Int(IntOp::DivU, alu_size, rs, rt)));
                    set_reg_alu_output!(Reg::Hi, node!(Int(IntOp::RemU, alu_size, rs, rt)));
                    return Ok(state);
                }

                28 | 29 => {
                    // FIXME(eddyb) perform actual 128-bit multiplies, using
                    // `Sext(B128, ...)` for `funct=28`, and `Zext(B128, ...)`
                    // for `funct=29`, or emulate it using 64-bit operations only.
                    let result = node!(Int(IntOp::Mul, B64, rs, rt));
                    set_reg_alu_output!(Reg::Lo, result);
                    set_reg_alu_output!(Reg::Hi, cx.a(Const::new(B64, 0)));
                    return Ok(state);
                }

                32 | 33 | 44 | 45 => node!(Int(IntOp::Add, alu_size, rs, rt)),
                34 | 35 | 46 | 47 => node!(int_sub(rs, rt)),
                36 => node!(Int(IntOp::And, self.regs.size, rs, rt)),
                37 => node!(Int(IntOp::Or, self.regs.size, rs, rt)),
                38 => node!(Int(IntOp::Xor, self.regs.size, rs, rt)),
                39 => node!(bit_not(node!(Int(IntOp::Or, self.regs.size, rs, rt)))),
                42 => node!(Zext(
                    self.regs.size,
                    node!(Int(IntOp::LtS, self.regs.size, rs, rt))
                )),
                43 => node!(Zext(
                    self.regs.size,
                    node!(Int(IntOp::LtU, self.regs.size, rs, rt))
                )),

                60 => node!(Int(
                    IntOp::Shl,
                    alu_size,
                    rt,
                    cx.a(Const::new(B8, sa as u64 + 32))
                )),
                63 => node!(Int(
                    IntOp::ShrU,
                    alu_size,
                    rt,
                    cx.a(Const::new(B8, sa as u64 + 32))
                )),

                _ => error!("unknown SPECIAL funct={} (0b{0:06b} / 0x{0:02x})", funct),
            };
            set_reg_alu_output!(rd, v);
        } else if op == 1 {
            // REGIMM (I format w/o rt).
            let rs_was_zero = rs == 0;
            let rs = get_reg_native!(rs);
            match rt {
                0 | 16 => {
                    if (rt & 16) != 0 {
                        link!();
                    }
                    if rs_was_zero {
                        // Special-case `zero < zero` branches to noops - in the
                        // case of `BLTZAL $zero`, the "And Link" (`link!()`)
                        // effect may be the only reason the instruction is used.
                        // HACK(eddyb) this is done here to avoid const-folding
                        // away control-flow in the general case.
                        return Ok(state);
                    }
                    return branch!(node!(Int(IntOp::LtS, self.regs.size, rs, cx.a(Const::new(self.regs.size, 0)))) => true);
                }
                1 | 17 => {
                    if (rt & 16) != 0 {
                        link!();
                    }
                    if rs_was_zero {
                        // Special-case `zero >= zero` branches to jumps.
                        // HACK(eddyb) this is done here to avoid const-folding
                        // away control-flow in the general case.
                        return jump!(branch_target!());
                    }
                    return branch!(node!(Int(IntOp::LtS, self.regs.size, rs, cx.a(Const::new(self.regs.size, 0)))) => false);
                }
                _ => error!("unknown REGIMM rt={} (0b{0:06b} / 0x{0:02x})", rt),
            }
        } else if op == 2 || op == 3 {
            // J format.
            if op == 3 {
                link!();
            }
            return jump!(cx.a(Const::new(
                self.regs.size,
                (pc.as_u64() & !0x3fff_ffff) | ((field(0, 26) << 2) as u64)
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
                // HACK(eddyb) force `{get,set}_reg_alu_{input,output}` below into 64-bit mode.
                alu_size = B64;
            }

            if let 4..=7 | 10..=14 | 20..=23 = op {
                // HACK(eddyb) force `{get,set}_reg_alu_{input,output}` below into "native" mode.
                alu_size = self.regs.size;
            }

            let rd = rt;
            let rt = get_reg_alu_input!(rt);

            macro_rules! mem_ref {
                ($sz:ident) => {
                    MemRef {
                        mem: state.get(cx, self.mem),
                        mem_type: self.mem_type,
                        addr: node!(Int(
                            IntOp::Add,
                            self.mem_type.addr_size,
                            get_reg_native!(rs),
                            cx.a(imm16.sext(self.mem_type.addr_size))
                        )),
                        size: MemSize::$sz,
                    }
                };
            }

            match op {
                4..=7 | 20..=23 => {
                    let rs = get_reg_native!(rs);

                    // FIXME(eddyb) for 20..=23, only execute the delay slot when
                    // the branch is taken (the specs talk about "nullification").
                    let _is_likely = matches!(op, 20..=23);

                    let (cond, negate) = match op {
                        4 | 5 | 20 | 21 => (node!(Int(IntOp::Eq, self.regs.size, rs, rt)), false),
                        6 | 7 | 22 | 23 => (
                            node!(Int(
                                IntOp::LtS,
                                self.regs.size,
                                cx.a(Const::new(self.regs.size, 0)),
                                rs
                            )),
                            true,
                        ),
                        _ => unreachable!(),
                    };
                    let negate = match op {
                        4 | 6 | 20 | 22 => negate,
                        5 | 7 | 21 | 23 => !negate,
                        _ => unreachable!(),
                    };

                    return branch!(cond => !negate);
                }

                8..=14 | 24 | 25 => {
                    let op = match op {
                        8 | 9 | 24 | 25 => IntOp::Add,
                        10 => IntOp::LtS,
                        11 => IntOp::LtU,
                        12 => IntOp::And,
                        13 => IntOp::Or,
                        14 => IntOp::Xor,

                        _ => unreachable!(),
                    };
                    // HACK(eddyb) pick sign- or zero-extension based on op.
                    let imm32 = match op {
                        IntOp::And | IntOp::Or | IntOp::Xor => imm16.zext(B32),
                        _ => imm16.sext(B32),
                    };
                    let imm = imm32.sext(alu_size);

                    let rs = get_reg_alu_input!(rs);
                    let mut v = node!(Int(op, alu_size, rs, cx.a(imm)));
                    if cx[v].ty(cx) == Type::Bits(B1) {
                        v = node!(Zext(alu_size, v));
                    }
                    set_reg_alu_output!(rd, v);
                }
                15 => set_reg_alu_output!(rd, cx.a(Const::new(B32, (imm16.as_u32() << 16) as u64))),

                32 => set_reg_alu_output!(rd, node!(Sext(B32, node!(Load(mem_ref!(M8)))))),
                33 => set_reg_alu_output!(rd, node!(Sext(B32, node!(Load(mem_ref!(M16)))))),
                35 => set_reg_alu_output!(rd, node!(Load(mem_ref!(M32)))),
                36 => set_reg_alu_output!(rd, node!(Zext(B32, node!(Load(mem_ref!(M8)))))),
                37 => set_reg_alu_output!(rd, node!(Zext(B32, node!(Load(mem_ref!(M16)))))),

                40 => state.set(
                    cx,
                    self.mem,
                    node!(Store(mem_ref!(M8), node!(Trunc(B8, rt)))),
                ),
                41 => state.set(
                    cx,
                    self.mem,
                    node!(Store(mem_ref!(M16), node!(Trunc(B16, rt)))),
                ),
                43 => state.set(cx, self.mem, node!(Store(mem_ref!(M32), rt))),

                47 => {
                    // FIXME(eddyb) use the result of rs+imm as an argument.
                    return Err(Edges::One(Edge {
                        state,
                        effect: Effect::Opaque {
                            call: format!(
                                "CACHE(op={}, base={}, imm={:?})",
                                field(16, 5),
                                Reg::try_from(field(21, 5))
                                    .map(|r| &cx[cx[self.regs[r]].name])
                                    .unwrap_or_else(|ZeroReg| "zero"),
                                imm16,
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
                                Reg::try_from(field(21, 5))
                                    .map(|r| &cx[cx[self.regs[r]].name])
                                    .unwrap_or_else(|ZeroReg| "zero"),
                                imm16,
                            ),
                            next_pc: cx.a(*pc),
                        },
                    }));
                }

                55 => set_reg_alu_output!(rd, node!(Load(mem_ref!(M64)))),
                63 => state.set(cx, self.mem, node!(Store(mem_ref!(M64), rt))),

                _ => error!("unknown opcode {} (0b{0:06b} / 0x{0:02x})", op),
            }
        }

        Ok(state)
    }
}

pub mod i8051;
pub mod i8080;
pub mod mips;

use crate::ir::{BitSize, Const, Cx, Edge, Edges, Reg, State};
use crate::platform::Rom;

pub trait Isa {
    fn addr_size(&self) -> BitSize;

    fn regs(&self, cx: &Cx) -> Vec<Reg>;

    // FIXME(eddyb) replace the `Result` with a dedicated enum.
    fn lift_instr(
        &self,
        cx: &Cx,
        rom: &dyn Rom,
        pc: &mut Const,
        state: State,
    ) -> Result<State, Edges<Edge>>;
}

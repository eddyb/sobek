pub mod i8051;
pub mod i8080;
pub mod mips;

use crate::ir::{Const, Cx, Edge, Edges, IGlobal, State};
use crate::platform::Rom;

pub trait Isa {
    fn mem_containing_rom(&self) -> IGlobal;

    // FIXME(eddyb) replace the `Result` with a dedicated enum.
    fn lift_instr(
        &self,
        cx: &Cx,
        rom: &dyn Rom,
        pc: &mut Const,
        state: State,
    ) -> Result<State, Edges<Edge>>;
}

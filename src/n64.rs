use crate::ir::{Const, Cx, MemSize, Platform, Rom, UnsupportedAddress};
use crate::mips::Mips32;

pub struct Cartridge {
    pub big_endian: bool,
    pub data: Vec<u8>,
}

impl Cartridge {
    fn virtual_to_physical(&self, mut addr: Const) -> Const {
        match addr.0 {
            0x8000_0000..=0x9fff_ffff => addr.0 -= 0x8000_0000,
            0xa000_0000..=0xbfff_ffff => addr.0 -= 0xa000_0000,
            _ => {}
        }
        addr
    }

    fn load_physical(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        match addr.0 {
            0x0000_0400..=0x003f_ffff => Ok(self.load_raw(Const(0x1000 + (addr.0 - 0x400)), size)),
            _ => return Err(UnsupportedAddress(addr)),
        }
    }

    pub fn load_raw(&self, addr: Const, size: MemSize) -> Const {
        assert_eq!(size, MemSize::M32);
        assert_eq!(addr.0 & 3, 0);

        let b = |i| self.data[addr.0 as usize + i];
        let bytes = [b(0), b(1), b(2), b(3)];
        Const(if self.big_endian {
            u32::from_be_bytes(bytes)
        } else {
            u32::from_le_bytes(bytes)
        })
    }
}

impl Rom for Cartridge {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        self.load_physical(self.virtual_to_physical(addr), size)
    }
}

pub struct N64 {
    pub arch: Mips32,
    pub rom: Cartridge,
}

impl Platform for N64 {
    type Arch = Mips32;
    type Rom = Cartridge;

    fn arch(&self) -> &Self::Arch {
        &self.arch
    }
    fn rom(&self) -> &Self::Rom {
        &self.rom
    }
}

pub fn analyze(rom: Cartridge) {
    let mut cx = Cx::new(N64 { arch: Mips32, rom });
    let mut explorer = crate::explore::Explorer::new(&mut cx);
    let entry_pc = explorer.cx.platform.rom.load_raw(Const(8), MemSize::M32);
    explorer.explore_bbs(entry_pc);

    let mut last_end = *explorer.blocks.keys().next().unwrap();
    for (&entry_pc, bb) in &explorer.blocks {
        if last_end < entry_pc {
            println!("{:?} {{", last_end);
            println!("    /* {} unanalyzed bytes */", entry_pc.0 - last_end.0);
            println!("}}");
        }
        println!(
            "{:?} {}",
            entry_pc,
            cx.pretty_print(&bb.effect, Some(&bb.state.end))
        );
        last_end = bb.pc.end;
    }
}

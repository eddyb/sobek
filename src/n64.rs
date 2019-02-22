use crate::ir::{BitSize, Const, Cx, MemSize, Platform, Rom, UnsupportedAddress};
use crate::mips::Mips32;

pub struct Cartridge {
    pub big_endian: bool,
    pub data: Vec<u8>,
}

impl Cartridge {
    fn virtual_to_physical(&self, mut addr: u32) -> u32 {
        match addr {
            0x8000_0000..=0x9fff_ffff => addr -= 0x8000_0000,
            0xa000_0000..=0xbfff_ffff => addr -= 0xa000_0000,
            _ => {}
        }
        addr
    }

    fn load_physical(&self, addr: u32, size: MemSize) -> Result<Const, UnsupportedAddress> {
        match addr {
            0x0000_0400..=0x003f_ffff => Ok(self.load_raw(0x1000 + (addr - 0x400), size)),
            _ => return Err(UnsupportedAddress(Const::new(BitSize::B32, addr))),
        }
    }

    pub fn load_raw(&self, addr: u32, size: MemSize) -> Const {
        let b = |i| self.data[addr as usize + i];

        match size {
            MemSize::M8 => Const::new(BitSize::B8, b(0) as u32),
            MemSize::M16 => {
                assert_eq!(addr & 1, 0);

                let bytes = [b(0), b(1)];
                Const::new(
                    BitSize::B16,
                    if self.big_endian {
                        u16::from_be_bytes(bytes)
                    } else {
                        u16::from_le_bytes(bytes)
                    } as u32,
                )
            }
            MemSize::M32 => {
                assert_eq!(addr & 3, 0);

                let bytes = [b(0), b(1), b(2), b(3)];
                Const::new(
                    BitSize::B32,
                    if self.big_endian {
                        u32::from_be_bytes(bytes)
                    } else {
                        u32::from_le_bytes(bytes)
                    },
                )
            }
        }
    }
}

impl Rom for Cartridge {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        self.load_physical(self.virtual_to_physical(addr.zext32()), size)
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
    let entry_pc = explorer.cx.platform.rom.load_raw(8, MemSize::M32);
    explorer.explore_bbs(entry_pc);

    let mut last_end = *explorer.blocks.keys().next().unwrap();
    for (&entry_pc, bb) in &explorer.blocks {
        if last_end < entry_pc {
            println!("{:?} {{", last_end);
            println!(
                "    /* {} unanalyzed bytes */",
                entry_pc.zext32() - last_end.zext32()
            );
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

use crate::arch::mips::{AddrSpace, Mips32};
use crate::ir::{BitSize, Const, MemSize, Platform, Rom, UnsupportedAddress};

pub struct Cartridge {
    pub big_endian: bool,
    pub data: Vec<u8>,
}

impl Cartridge {
    fn load_physical(&self, addr: u32, size: MemSize) -> Result<Const, ()> {
        match addr {
            0x0000_0400..=0x003f_ffff => Ok(self.load_raw(0x1000 + (addr - 0x400), size)),
            _ => Err(()),
        }
    }

    pub fn load_raw(&self, addr: u32, size: MemSize) -> Const {
        let b = |i| self.data[addr as usize + i];

        // FIXME(eddyb) deduplicate these if possible.
        match size {
            MemSize::M8 => Const::new(BitSize::B8, b(0) as u64),
            MemSize::M16 => {
                assert_eq!(addr & 1, 0);

                let bytes = [b(0), b(1)];
                Const::new(
                    BitSize::B16,
                    if self.big_endian {
                        u16::from_be_bytes(bytes)
                    } else {
                        u16::from_le_bytes(bytes)
                    } as u64,
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
                    } as u64,
                )
            }
            MemSize::M64 => {
                assert_eq!(addr & 7, 0);

                let bytes = [b(0), b(1), b(2), b(3), b(4), b(5), b(6), b(7)];
                Const::new(
                    BitSize::B64,
                    if self.big_endian {
                        u64::from_be_bytes(bytes)
                    } else {
                        u64::from_le_bytes(bytes)
                    },
                )
            }
        }
    }

    pub fn entry_pc(&self) -> Const {
        self.load_raw(8, MemSize::M32)
    }
}

impl Rom for Cartridge {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        let err = UnsupportedAddress(addr);
        let (addr_space, addr) = Mips32::decode_addr(addr.as_u32());
        match addr_space {
            AddrSpace::Direct { .. } => self.load_physical(addr, size).map_err(|_| err),
            AddrSpace::Mapped(_) => Err(err),
        }
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

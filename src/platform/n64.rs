use crate::arch::mips::{AddrSpace, Mips32};
use crate::ir::{BitSize, Const, MemSize, RawRom, Rom, SimplePlatform, UnsupportedAddress};

pub struct Cartridge {
    pub raw: RawRom<Vec<u8>>,
}

impl Cartridge {
    fn load_physical(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        match addr.as_u32() {
            addr @ 0x0000_0400..=0x003f_ffff => self.raw.load(
                Const::new(BitSize::B32, (0x1000 + (addr - 0x400)) as u64),
                size,
            ),
            _ => Err(UnsupportedAddress(addr)),
        }
    }

    pub fn entry_pc(&self) -> Const {
        self.raw
            .load(Const::new(BitSize::B32, 8), MemSize::M32)
            .unwrap()
    }
}

impl Rom for Cartridge {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        let err = UnsupportedAddress(addr);
        let (addr_space, addr) = Mips32::decode_addr(addr.as_u32());
        match addr_space {
            AddrSpace::Direct { .. } => self
                .load_physical(Const::new(BitSize::B32, addr as u64), size)
                .map_err(|_| err),
            AddrSpace::Mapped(_) => Err(err),
        }
    }
}

pub type N64 = SimplePlatform<Mips32, Cartridge>;

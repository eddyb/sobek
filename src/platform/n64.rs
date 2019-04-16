use crate::ir::{BitSize, Const, MemSize, RawRom, Rom, SimplePlatform, UnsupportedAddress};
use crate::isa::mips::{AddrSpace, Mips32};

pub struct Cartridge {
    pub raw: RawRom<Vec<u8>>,
    pub base: Const,
}

impl Cartridge {
    pub fn new(raw: RawRom<Vec<u8>>) -> Self {
        let base = raw.load(Const::new(BitSize::B32, 8), MemSize::M32).unwrap();
        Cartridge { raw, base }
    }

    fn load_physical(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        // FIXME(eddyb) do this only once.
        let (base_addr_space, base) = Mips32::decode_addr(self.base.as_u32());
        assert_eq!(base_addr_space, AddrSpace::Direct { cached: true });

        match addr.as_u32() {
            // TODO(eddyb) make sure this is actually correct now.
            addr @ 0..=0x003f_ffff if addr >= base => self.raw.load(
                Const::new(BitSize::B32, (0x1000 + (addr - base)) as u64),
                size,
            ),
            _ => Err(UnsupportedAddress(addr)),
        }
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

use crate::ir::{BitSize, Const, MemSize, MemType};
use crate::isa::mips::{AddrSpace, Mips32};
use crate::platform::{RawRom, Rom, SimplePlatform, UnsupportedAddress};
use std::ops::Deref;

pub struct Cartridge<R: Deref<Target = [u8]>> {
    pub raw: RawRom<R>,
    pub base: Const,
}

impl<R: Deref<Target = [u8]>> Cartridge<R> {
    pub fn new(raw: RawRom<R>) -> Self {
        let base = raw
            .load(
                MemType {
                    addr_size: BitSize::B32,
                    big_endian: true,
                },
                Const::new(BitSize::B32, 8),
                MemSize::M32,
            )
            .unwrap();
        Cartridge { raw, base }
    }

    fn load_physical(
        &self,
        mem_type: MemType,
        addr: Const,
        size: MemSize,
    ) -> Result<Const, UnsupportedAddress> {
        // FIXME(eddyb) do this only once.
        let (base_addr_space, base) = Mips32::decode_addr(self.base.as_u32());
        assert_eq!(base_addr_space, AddrSpace::Direct { cached: true });

        match addr.as_u32() {
            // TODO(eddyb) make sure this is actually correct now.
            addr @ 0..=0x003f_ffff if addr >= base => self.raw.load(
                mem_type,
                Const::new(BitSize::B32, (0x1000 + (addr - base)) as u64),
                size,
            ),
            _ => Err(UnsupportedAddress(addr)),
        }
    }
}

impl<R: Deref<Target = [u8]>> Rom for Cartridge<R> {
    fn load(
        &self,
        mem_type: MemType,
        addr: Const,
        size: MemSize,
    ) -> Result<Const, UnsupportedAddress> {
        let err = UnsupportedAddress(addr);
        let (addr_space, addr) = Mips32::decode_addr(addr.as_u32());
        match addr_space {
            AddrSpace::Direct { .. } => self
                .load_physical(mem_type, Const::new(BitSize::B32, addr as u64), size)
                .map_err(|_| err),
            AddrSpace::Mapped(_) => Err(err),
        }
    }
}

pub type N64<R> = SimplePlatform<Mips32, Cartridge<R>>;

use crate::ir::{BitSize, Const, Cx, MemSize, MemType};
use crate::isa::mips::{AddrSpace, Mips};
use crate::isa::Isa;
use crate::platform::{Platform, RawRom, Rom, UnsupportedAddress};
use std::ops::Deref;

pub struct Cartridge<R: Deref<Target = [u8]>> {
    pub raw: RawRom<R>,
    pub base: Const,
}

impl<R: Deref<Target = [u8]>> Cartridge<R> {
    pub fn new(raw: RawRom<R>) -> Self {
        let base32 = raw
            .load(
                MemType {
                    addr_size: BitSize::B32,
                    big_endian: true,
                },
                Const::new(BitSize::B32, 8),
                MemSize::M32,
            )
            .unwrap();
        // Sign-extend to a 64-bit address to preserve address decoding properties.
        // FIXME(eddyb) it might be better to have a forced 32-bit-addresses
        // 64-bit registers MIPS mode, and always truncate addr on load/store.
        let base = base32.sext(BitSize::B64);
        Cartridge { raw, base }
    }

    fn load_physical(
        &self,
        mem_type: MemType,
        addr: Const,
        size: MemSize,
    ) -> Result<Const, UnsupportedAddress> {
        // FIXME(eddyb) do this only once.
        // FIXME(eddyb) use `decode_virtual_addr64` when it becomes available.
        let (base_addr_space, base) = {
            let virtual_addr64 = self.base.sext(BitSize::B64);
            let virtual_addr32 = self.base.trunc(BitSize::B32);

            // FIXME(eddyb) support addresses other than the 32->64 compatibility
            // subset (i.e. a sign-extended 32-bit address).
            if virtual_addr32.sext(BitSize::B64) != virtual_addr64 {
                return Err(UnsupportedAddress(addr));
            }

            Mips::decode_virtual_addr32(virtual_addr32.as_u32())
        };
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

        // FIXME(eddyb) use `decode_virtual_addr64` when it becomes available.
        let (addr_space, addr) = {
            let virtual_addr64 = addr.sext(BitSize::B64);
            let virtual_addr32 = addr.trunc(BitSize::B32);

            // FIXME(eddyb) support addresses other than the 32->64 compatibility
            // subset (i.e. a sign-extended 32-bit address).
            if virtual_addr32.sext(BitSize::B64) != virtual_addr64 {
                return Err(UnsupportedAddress(addr));
            }

            let (addr_space, addr) = Mips::decode_virtual_addr32(virtual_addr32.as_u32());
            (addr_space, Const::new(BitSize::B32, addr as u64))
        };

        match addr_space {
            AddrSpace::Direct { .. } => self.load_physical(mem_type, addr, size).map_err(|_| err),
            AddrSpace::Mapped(_) => Err(err),
        }
    }
}

// FIXME(eddyb) this is only different from `SimplePlatform` in providing
// a custom constructor.
pub struct N64<R: Deref<Target = [u8]>> {
    pub isa: Mips,
    pub rom: Cartridge<R>,
}

impl<R: Deref<Target = [u8]>> Platform for N64<R> {
    fn isa(&self) -> &dyn Isa {
        &self.isa
    }
    fn rom(&self) -> &dyn Rom {
        &self.rom
    }
}

impl<R: Deref<Target = [u8]>> N64<R> {
    pub fn new(cx: &Cx, rom: Cartridge<R>) -> Self {
        N64 {
            isa: Mips::new_64be(cx),
            rom,
        }
    }
}

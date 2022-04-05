pub mod n64;

use crate::ir::{BitSize, Const, MemSize};
use crate::isa::Isa;
use std::ops::Deref;

#[derive(Debug)]
pub struct UnsupportedAddress(pub Const);

pub trait Rom {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress>;
}

pub struct RawRom<
    // FIXME(eddyb) use an `enum` when they're allowed in const generics on stable.
    const BIG_ENDIAN: bool,
    T,
> {
    pub data: T,
}

impl<const BIG_ENDIAN: bool, T> From<T> for RawRom<BIG_ENDIAN, T> {
    fn from(data: T) -> Self {
        Self { data }
    }
}

pub type RawRomLe<T> = RawRom<false, T>;
pub type RawRomBe<T> = RawRom<true, T>;

impl<const BIG_ENDIAN: bool, T: Deref<Target = [u8]>> Rom for RawRom<BIG_ENDIAN, T> {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        let err = UnsupportedAddress(addr);
        let addr = addr.as_u64();
        if addr >= self.data.len() as u64
            || addr + (size.bytes() - 1) as u64 >= self.data.len() as u64
        {
            return Err(err);
        }
        let b = |i| self.data[addr as usize + i];

        // FIXME(eddyb) deduplicate these if possible.
        Ok(match size {
            MemSize::M8 => Const::new(BitSize::B8, b(0) as u64),
            MemSize::M16 => {
                assert_eq!(addr & 1, 0);

                let bytes = [b(0), b(1)];
                Const::new(
                    BitSize::B16,
                    if BIG_ENDIAN {
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
                    if BIG_ENDIAN {
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
                    if BIG_ENDIAN {
                        u64::from_be_bytes(bytes)
                    } else {
                        u64::from_le_bytes(bytes)
                    },
                )
            }
        })
    }
}

pub trait Platform {
    fn isa(&self) -> &dyn Isa;
    fn rom(&self) -> &dyn Rom;
}

pub struct SimplePlatform<A, R> {
    pub isa: A,
    pub rom: R,
}

impl<A: Isa, R: Rom> Platform for SimplePlatform<A, R> {
    fn isa(&self) -> &dyn Isa {
        &self.isa
    }
    fn rom(&self) -> &dyn Rom {
        &self.rom
    }
}

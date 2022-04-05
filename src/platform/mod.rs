pub mod n64;

use crate::ir::{Const, MemSize};
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
    T = memmap2::Mmap,
> {
    pub data: T,
}

impl<const BIG_ENDIAN: bool, T> From<T> for RawRom<BIG_ENDIAN, T> {
    fn from(data: T) -> Self {
        Self { data }
    }
}

pub type RawRomLe<T = memmap2::Mmap> = RawRom<false, T>;
pub type RawRomBe<T = memmap2::Mmap> = RawRom<true, T>;

impl<const BIG_ENDIAN: bool> RawRom<BIG_ENDIAN> {
    pub fn mmap_file(path: impl AsRef<std::path::Path>) -> std::io::Result<Self> {
        let file = std::fs::File::open(path)?;
        // FIXME(eddyb) is this safe? ideally "read-only CoW" would enforce that.
        let data = unsafe { memmap2::MmapOptions::new().map_copy_read_only(&file)? };
        Ok(Self { data })
    }
}

impl<const BIG_ENDIAN: bool, T: Deref<Target = [u8]>> Rom for RawRom<BIG_ENDIAN, T> {
    fn load(&self, addr: Const, size: MemSize) -> Result<Const, UnsupportedAddress> {
        let err = UnsupportedAddress(addr);
        let addr = addr.as_u64();
        let bytes = usize::try_from(addr)
            .ok()
            .and_then(|addr| self.data.get(addr..)?.get(..usize::from(size.bytes())))
            .ok_or(err)?;

        macro_rules! from_bytes {
            ($uint:ty) => {{
                assert_eq!(addr & (size.bytes() - 1) as u64, 0);

                let &bytes = bytes.try_into().unwrap();

                (if BIG_ENDIAN {
                    <$uint>::from_be_bytes(bytes)
                } else {
                    <$uint>::from_le_bytes(bytes)
                } as u64)
            }};
        }
        Ok(Const::new(
            size.into(),
            match size {
                MemSize::M8 => bytes[0] as u64,
                MemSize::M16 => from_bytes!(u16),
                MemSize::M32 => from_bytes!(u32),
                MemSize::M64 => from_bytes!(u64),
            },
        ))
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

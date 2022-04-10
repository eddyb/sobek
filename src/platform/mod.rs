pub mod n64;
pub mod unix;

use crate::ir::{Const, MemSize, MemType};
use crate::isa::Isa;
use std::ops::Deref;

#[derive(Debug)]
pub struct UnsupportedAddress(pub Const);

pub trait Rom {
    fn load(
        &self,
        mem_type: MemType,
        addr: Const,
        size: MemSize,
    ) -> Result<Const, UnsupportedAddress>;
}

pub struct RawRom<R: Deref<Target = [u8]>>(pub R);

impl RawRom<memmap2::Mmap> {
    pub fn mmap_file(path: impl AsRef<std::path::Path>) -> std::io::Result<Self> {
        let file = std::fs::File::open(path)?;
        // FIXME(eddyb) is this safe? ideally "read-only CoW" would enforce that.
        let data = unsafe { memmap2::MmapOptions::new().map_copy_read_only(&file)? };
        Ok(Self(data))
    }
}

impl<R: Deref<Target = [u8]>> Rom for RawRom<R> {
    fn load(
        &self,
        mem_type: MemType,
        addr: Const,
        size: MemSize,
    ) -> Result<Const, UnsupportedAddress> {
        let err = UnsupportedAddress(addr);
        let addr = addr.as_u64();
        let bytes = usize::try_from(addr)
            .ok()
            .and_then(|addr| self.0.get(addr..)?.get(..usize::from(size.bytes())))
            .ok_or(err)?;

        macro_rules! from_bytes {
            ($uint:ty) => {{
                let &bytes = bytes.try_into().unwrap();

                if mem_type.big_endian {
                    <$uint>::from_be_bytes(bytes)
                } else {
                    <$uint>::from_le_bytes(bytes)
                }
                .into()
            }};
        }
        Ok(Const::new(
            size.into(),
            match size {
                MemSize::M8 => bytes[0].into(),
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

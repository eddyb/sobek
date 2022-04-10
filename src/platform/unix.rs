//! UNIX userspace processes, loaded from executable "images" (e.g. ELF).

use crate::ir::{Const, MemSize, MemType};
use crate::platform::{RawRom, Rom, SimplePlatform, UnsupportedAddress};
use object::{Object, ObjectSegment};
use std::ops::Range;

pub struct Executable<'a> {
    pub virtual_to_raw_file: Vec<(Range<u64>, RawRom<&'a [u8]>)>,
    pub virtual_entry: u64,
}

impl<'a> Executable<'a> {
    pub fn load_at_virtual_addr(raw_file: RawRom<&'a [u8]>, virtual_base_addr: u64) -> Self {
        let obj_file = object::File::parse(raw_file.0).unwrap();
        let virtual_to_raw_file = obj_file
            .segments()
            .map(|segment| {
                let virtual_start = virtual_base_addr.checked_add(segment.address()).unwrap();
                let (file_start, file_size) = segment.file_range();
                let (file_start, file_size) = (
                    usize::try_from(file_start).unwrap(),
                    usize::try_from(file_size).unwrap(),
                );
                (
                    virtual_start..virtual_start.checked_add(segment.size()).unwrap(),
                    RawRom(&raw_file.0[file_start..][..file_size]),
                )
            })
            .collect();
        let virtual_entry = virtual_base_addr.checked_add(obj_file.entry()).unwrap();

        Executable {
            virtual_to_raw_file,
            virtual_entry,
        }
    }
}

impl Rom for Executable<'_> {
    fn load(
        &self,
        mem_type: MemType,
        addr: Const,
        size: MemSize,
    ) -> Result<Const, UnsupportedAddress> {
        self.virtual_to_raw_file
            .iter()
            .find_map(|(virtual_range, raw_segment)| {
                let addr = addr.as_u64();
                if virtual_range.contains(&addr) {
                    let segment_offset = Const::new(mem_type.addr_size, addr - virtual_range.start);
                    Some(raw_segment.load(mem_type, segment_offset, size))
                } else {
                    None
                }
            })
            .ok_or(UnsupportedAddress(addr))?
    }
}

pub type UnixProcess<'a, A> = SimplePlatform<A, Executable<'a>>;

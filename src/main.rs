use sobek::arch::mips::Mips32;
use sobek::arch::_8051::_8051;
use sobek::arch::_8080::_8080;
use sobek::explore::{BlockId, Explorer};
use sobek::ir::{BitSize, Const, Cx, Platform, RawRom, SimplePlatform};
use sobek::platform::n64::{self, N64};
use std::iter;

fn analyze_and_dump<P: Platform>(platform: P, entries: impl Iterator<Item = Const>) {
    let mut cx = Cx::new(platform);
    let mut explorer = Explorer::new(&mut cx);
    for entry_pc in entries {
        explorer.explore_bbs(entry_pc);
    }

    let mut last_end = explorer.blocks.keys().next().unwrap().entry_pc;
    for (&bb, block) in &explorer.blocks {
        if last_end < bb.entry_pc {
            println!("{:?} {{", BlockId { entry_pc: last_end });
            println!("    /* {} unanalyzed bytes */", bb.entry_pc - last_end);
            println!("}}");
        }
        println!(
            "{:?} {}",
            bb,
            cx.pretty_print_on_edges(block.edges.as_ref().map(|e, _| (&e.state, &e.effect)))
        );
        last_end = block.pc.end.as_u64();
    }
}

fn main() {
    // FIXME(eddyb) switch to `structopt`.
    let arch = std::env::args().nth(1).unwrap();
    let path = std::env::args().nth(2).unwrap();
    let data = std::fs::read(path).unwrap();
    match &arch[..] {
        "8051" => {
            analyze_and_dump(
                SimplePlatform {
                    arch: _8051,
                    rom: RawRom {
                        big_endian: false,
                        data,
                    },
                },
                iter::once(Const::new(BitSize::B16, 0)),
            );
        }
        "8080" => {
            analyze_and_dump(
                SimplePlatform {
                    arch: _8080 {
                        flavor: sobek::arch::_8080::Flavor::Intel,
                    },
                    rom: RawRom {
                        big_endian: false,
                        data,
                    },
                },
                iter::once(Const::new(BitSize::B16, 0)),
            );
        }
        "gb" => {
            analyze_and_dump(
                SimplePlatform {
                    arch: _8080 {
                        flavor: sobek::arch::_8080::Flavor::LR35902,
                    },
                    rom: RawRom {
                        big_endian: false,
                        data,
                    },
                },
                iter::once(0x100)
                    .chain((0..5).map(|i| 0x40 + i * 8))
                    .map(|x| Const::new(BitSize::B16, x)),
            );
        }
        "n64" => {
            let rom = n64::Cartridge {
                raw: RawRom {
                    big_endian: true,
                    data,
                },
            };
            let entry_pc = rom.entry_pc();
            analyze_and_dump(N64 { arch: Mips32, rom }, iter::once(entry_pc));
        }
        _ => panic!("unsupport arch {:?}", arch),
    }
}

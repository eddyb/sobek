use sobek::arch::mips::Mips32;
use sobek::explore::{BlockId, Explorer};
use sobek::ir::{BitSize, Const, Cx, Platform, RawRom};
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
            cx.pretty_print(&block.effect, Some(&block.state.end))
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

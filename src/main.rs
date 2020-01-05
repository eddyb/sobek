use sobek::explore::Explorer;
use sobek::ir::{BitSize, Const, Cx};
use sobek::isa::i8051::I8051;
use sobek::isa::i8080::I8080;
use sobek::isa::mips::Mips32;
use sobek::isa::Isa;
use sobek::platform::n64;
use sobek::platform::{RawRom, Rom, SimplePlatform};
use std::iter;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn analyze_and_dump(isa: impl Isa, rom: impl Rom, entries: impl Iterator<Item = Const>) {
    let cx = Cx::new();
    let platform = SimplePlatform { isa, rom };

    let cancel_token = Arc::new(AtomicBool::new(false));
    let ctrcc_result = {
        let cancel_token = cancel_token.clone();
        ctrlc::set_handler(move || {
            eprintln!("Ctrl-C: cancelling...");
            cancel_token.store(true, Ordering::SeqCst);
        })
    };
    match &ctrcc_result {
        Ok(()) => eprintln!("Press Ctrl-C at any time to cancel analysis"),
        Err(e) => eprintln!("warning: Ctrl-C not handled: {}", e),
    }
    let cancel_token = ctrcc_result.ok().map(|_| &*cancel_token);

    let mut explorer = Explorer::new(&cx, &platform, cancel_token);
    for entry_pc in entries {
        explorer.explore_bbs(entry_pc);
    }

    explorer.split_overlapping_bbs();

    let nester = sobek::nest::Nester::new(&explorer);

    let mut nested_pc = ..Const::new(
        platform.isa.addr_size(),
        explorer.blocks.keys().next().unwrap().entry_pc,
    );
    let mut last_end = nested_pc.end.as_u64();
    for (&bb, block) in &explorer.blocks {
        // Skip blocks in the last printed PC range, *unless* they overlap the
        // previous block (e.g. due to jumps into the middle of an instruction).
        if bb.entry_pc >= nested_pc.end.as_u64() || last_end > bb.entry_pc {
            println!("{}", nester.nested_block_to_string(bb, &mut nested_pc));
        }
        last_end = block.pc.end.as_u64();
    }
}

fn main() {
    // FIXME(eddyb) switch to `structopt`.
    let isa = std::env::args().nth(1).unwrap();
    let path = std::env::args().nth(2).unwrap();
    let data = std::fs::read(path).unwrap();
    match &isa[..] {
        "8051" => {
            analyze_and_dump(
                I8051,
                RawRom {
                    big_endian: false,
                    data,
                },
                iter::once(Const::new(BitSize::B16, 0)),
            );
        }
        "8080" => {
            analyze_and_dump(
                I8080 {
                    flavor: sobek::isa::i8080::Flavor::Intel,
                },
                RawRom {
                    big_endian: false,
                    data,
                },
                iter::once(Const::new(BitSize::B16, 0)),
            );
        }
        "gb" => {
            analyze_and_dump(
                I8080 {
                    flavor: sobek::isa::i8080::Flavor::LR35902,
                },
                RawRom {
                    big_endian: false,
                    data,
                },
                iter::once(0x100)
                    .chain((0..5).map(|i| 0x40 + i * 8))
                    .map(|x| Const::new(BitSize::B16, x)),
            );
        }
        "n64" => {
            let rom = n64::Cartridge::new(RawRom {
                big_endian: true,
                data,
            });
            let entry_pc = rom.base;
            analyze_and_dump(Mips32, rom, iter::once(entry_pc));
        }
        _ => panic!("unsupport isa {:?}", isa),
    }
}

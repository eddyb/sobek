use sobek::explore::Explorer;
use sobek::ir::{BitSize, Const, Cx, Isa, Platform, RawRom, SimplePlatform};
use sobek::isa::i8051::I8051;
use sobek::isa::i8080::I8080;
use sobek::isa::mips::Mips32;
use sobek::platform::n64::{self, N64};
use std::iter;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn analyze_and_dump<P: Platform>(platform: P, entries: impl Iterator<Item = Const>) {
    let cx = Cx::new(platform);

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

    let mut explorer = Explorer::new(&cx, cancel_token);
    for entry_pc in entries {
        explorer.explore_bbs(entry_pc);
    }

    explorer.split_overlapping_bbs();

    let mut nester = sobek::nest::Nester::new(&explorer);

    let mut pc = ..Const::new(
        P::Isa::ADDR_SIZE,
        explorer.blocks.keys().next().unwrap().entry_pc,
    );
    for bb in nester.root_nested_blocks() {
        println!("{}", nester.nested_block_to_string(bb, &mut pc));
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
                SimplePlatform {
                    isa: I8051,
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
                    isa: I8080 {
                        flavor: sobek::isa::i8080::Flavor::Intel,
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
                    isa: I8080 {
                        flavor: sobek::isa::i8080::Flavor::LR35902,
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
            let rom = n64::Cartridge::new(RawRom {
                big_endian: true,
                data,
            });
            let entry_pc = rom.base;
            analyze_and_dump(N64 { isa: Mips32, rom }, iter::once(entry_pc));
        }
        _ => panic!("unsupport isa {:?}", isa),
    }
}

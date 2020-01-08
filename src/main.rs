use sobek::explore::Explorer;
use sobek::ir::{BitSize, Const, Cx};
use sobek::isa::i8051::I8051;
use sobek::isa::i8080::I8080;
use sobek::isa::mips::Mips32;
use sobek::isa::Isa;
use sobek::platform::n64;
use sobek::platform::{RawRom, Rom, SimplePlatform};
use std::iter;
use std::ops::Range;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

// FIXME(eddyb) better error types.
fn parse_addr(s: &str) -> Result<u64, String> {
    if s.starts_with("0x") {
        let s = &s[2..];
        // FIXME(eddyb) make this cheaper somehow.
        let s = &s.replace('_', "");
        u64::from_str_radix(s, 16).map_err(|e| e.to_string())
    } else {
        Err("addresses must start with `0x`".to_string())
    }
}

// FIXME(eddyb) better error types.
fn parse_addr_range(s: &str) -> Result<Range<u64>, String> {
    let mut parts = s.split("..");
    match (parts.next(), parts.next(), parts.next()) {
        (Some(start), Some(end), None) => Ok(parse_addr(start)?..parse_addr(end)?),
        _ => Err("address ranges must be `start..end`".to_string()),
    }
}

#[derive(structopt::StructOpt)]
struct Args {
    /// Platform to analyze for.
    #[structopt(short, long, name = "PLATFORM")]
    platform: Option<String>,

    /// Memory range to treat as an array.
    #[structopt(short, long, name = "ARRAY")]
    #[structopt(number_of_values(1), parse(try_from_str = parse_addr_range))]
    array: Vec<Range<u64>>,

    /// ROM file.
    #[structopt(parse(from_os_str), name = "ROM")]
    rom: PathBuf,
}

fn analyze_and_dump<I: Isa>(
    args: &Args,
    mk_isa: impl FnOnce(&Cx) -> I,
    rom: impl Rom,
    entries: impl Iterator<Item = Const>,
) {
    let cx = Cx::new();
    let platform = SimplePlatform {
        isa: mk_isa(&cx),
        rom,
    };

    let cancel_token = Arc::new(AtomicBool::new(false));
    let ctrcc_result = {
        let cancel_token = cancel_token.clone();
        ctrlc::set_handler(move || {
            eprintln!("  (Ctrl-C: cancelling...)");
            cancel_token.store(true, Ordering::SeqCst);
        })
    };
    match &ctrcc_result {
        Ok(()) => eprintln!("Press Ctrl-C at any time to cancel analysis"),
        Err(e) => eprintln!("warning: Ctrl-C not handled: {}", e),
    }
    let cancel_token = ctrcc_result.ok().map(|_| &*cancel_token);

    let mut explorer = Explorer::new(&cx, &platform, cancel_token);

    for array in &args.array {
        explorer
            .array_len
            .insert(array.start, array.end - array.start);
    }

    for entry_pc in entries {
        explorer.explore_bbs(entry_pc);
    }

    explorer.split_overlapping_bbs();

    let nester = sobek::nest::Nester::new(&explorer);

    let mut nested_pc = ..Const::new(
        cx[platform.isa.mem_containing_rom()]
            .ty
            .mem_addr_size()
            .unwrap(),
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

#[paw::main]
fn main(args: Args) {
    let data = std::fs::read(&args.rom).unwrap();
    let platform = match &args.platform {
        Some(p) => &p[..],
        None => panic!("unable auto-detect platform (NYI)"),
    };
    match platform {
        "8051" => {
            analyze_and_dump(
                &args,
                I8051::new,
                RawRom {
                    big_endian: false,
                    data,
                },
                iter::once(Const::new(BitSize::B16, 0)),
            );
        }
        "8080" => {
            analyze_and_dump(
                &args,
                I8080::new,
                RawRom {
                    big_endian: false,
                    data,
                },
                iter::once(Const::new(BitSize::B16, 0)),
            );
        }
        "gb" => {
            analyze_and_dump(
                &args,
                I8080::new_lr35902,
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
            analyze_and_dump(&args, Mips32::new, rom, iter::once(entry_pc));
        }
        _ => panic!("unsupported platform `{}`", platform),
    }
}

fn main() {
    let path = std::env::args().nth(1).unwrap();
    sobek::n64::analyze(sobek::n64::Cartridge {
        big_endian: true,
        data: std::fs::read(path).unwrap(),
    });
}

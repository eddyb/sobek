fn main() {
    let path = std::env::args().nth(1).unwrap();
    sobek::platform::n64::analyze(sobek::platform::n64::Cartridge {
        big_endian: true,
        data: std::fs::read(path).unwrap(),
    });
}

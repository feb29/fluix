use super::*;

fn check_varint<V: varint::Varint + PartialEq>(v: V) -> bool {
    let mut buf = vec![0u8; varint::MAX_VARINT_LEN16];
    let n = varint::encode(&mut buf, &v);
    let (d, m) = varint::decode(&buf[..n]).unwrap();
    v == d && n == m
}

quickcheck!{
    fn uvarint(v16: u16, v32: u32, v64: u64) -> bool {
        check_varint(v16) && check_varint(v32) && check_varint(v64)
    }
    fn ivarint(v16: i16, v32: i32, v64: i64) -> bool {
        check_varint(v16) && check_varint(v32) && check_varint(v64)
    }
}

fn test_debug(v: u32) {
    let mut buf = [0; 4];
    let n = stream_vbyte::encode_scalar(&mut buf[..], v);
    print!("[");
    for byte in &buf[..n] {
        print!(" {:08b}", byte);
    }
    println!(" ]");
}

#[test]
fn debug_vbyte_scalar() {
    test_debug(0);
    test_debug((1 << 16) - 1);
    test_debug((1 << 16) + 3);
    test_debug(std::u32::MAX);
}

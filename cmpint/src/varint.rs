//! This module implements a simple "varint" encoding of integers.
//! The encoding is:
//! - unsigned integers are serialized 7 bits at a time, starting with the
//!   least significant bits
//! - the most significant bit (msb) in each output byte indicates if there
//!   is a continuation byte (msb = 1)
//! - signed integers are mapped to unsigned integers using "zig-zag" encoding:
//!   Positive values x are written as 2*x + 0, negative values
//!   are written as 2*(^x) + 1; that is, negative numbers are complemented
//!   and whether to complement is encoded in bit 0.

// MaxVarintLenN is the maximum length of a varint-encoded N-bit integer.
pub const MAX_VARINT_LEN16: usize = 3;
pub const MAX_VARINT_LEN32: usize = 5;
pub const MAX_VARINT_LEN64: usize = 10;

pub trait Varint: Sized {
    fn encode(&self, buf: &mut [u8]) -> usize;
    fn decode(buf: &[u8]) -> Result<(Self, usize), usize>;
    // fn read_from<R: std::io::Read>(r: R) -> std::io::Result<(Self, usize)>;
}

pub fn encode<V: Varint>(buf: &mut [u8], v: &V) -> usize {
    <V as Varint>::encode(v, buf)
}

pub fn decode<V: Varint>(buf: &[u8]) -> Result<(V, usize), usize> {
    <V as Varint>::decode(buf)
}

// fn invalid_data(msg: &str) -> io::Error {
//     io::Error::new(io::ErrorKind::InvalidData, msg)
// }

macro_rules! impl_Varint {
    ( $( ($u:ty, $i:ty) ),* ) => ($(
        #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
        impl Varint for $u {
            /// Encodes self into buf and returns the number of bytes written.
            ///
            /// # Panic
            /// If the buffer is too small, encode will panic.
            fn encode(&self, buf: &mut [u8]) -> usize {
                let mut x = *self;
                let mut i = 0;
                while x >= 0x80 {
                    buf[i] = x as u8 | 0x80;
                    x >>= 7;
                    i += 1;
                }
                buf[i] = x as u8;
                i + 1
            }

            /// Decodes self from buf and returns a pair of value and the
            /// number of bytes read (> 0).
            /// If an error occurred, return the number of bytes only.
            /// n == 0: the buffer is too small.
            /// n  > 0: overflow.
            fn decode(buf: &[u8]) -> Result<(Self, usize), usize> {
                let mut x: $u = 0;
                let mut s = 0usize;

                for (i, &b) in buf.iter().enumerate() {
                    if b < 0x80 {
                        if i > 9 || i == 9 && b > 1 {
                            return Err(i + 1); // overflow
                        }
                        return Ok((x | (b as $u) << s, i + 1));
                    }
                    x |= (b & 0x7f) as $u << s;
                    s += 7;
                }
                Err(0)
            }

            // fn read_from<R: io::Read>(r: R) -> io::Result<(Self, usize)> {
            //     let mut x: $u = 0;
            //     let mut s = 0usize;
            //     for (i, byte) in r.bytes().enumerate() {
            //         let b = byte?;
            //         if b < 0x80 {
            //             if i > 9 || i == 9 && b > 1 {
            //                 return Err(invalid_data("varint overflow"))
            //             }
            //             return Ok((x | (b as $u) << s, i + 1));
            //         }
            //         x |= (b & 0x7f) as $u << s;
            //         s += 7;
            //     }
            //     Err(invalid_data("buffer too small"))
            // }
        }

        #[cfg_attr(feature = "cargo-clippy", allow(cast_lossless))]
        impl Varint for $i {
            /// Encodes self into buf and returns the number of bytes written.
            ///
            /// # Panic
            /// If the buffer is too small, encode will panic.
            fn encode(&self, buf: &mut [u8]) -> usize {
                let mut u = (*self as $u) << 1;
                if *self < 0 {
                    u = !u;
                }
                u.encode(buf)
            }

            /// Decodes self from buf and returns a pair of value and the
            /// number of bytes read (> 0).
            /// If an error occurred, return the number of bytes only.
            /// n == 0: the buffer is too small.
            /// n  > 0: overflow.
            fn decode(buf: &[u8]) -> Result<(Self, usize), usize> {
                <$u as Varint>::decode(buf).map(|(v, n)| {
                    let mut x = (v >> 1) as $i;
                    if v & 1 != 0 {
                        x = !x;
                    }
                    (x, n)
                })
            }

            // fn read_from<R: io::Read>(r: R) -> io::Result<(Self, usize)> {
            //     <$u as Varint>::read_from(r).map(|(v, n)|{
            //         let mut x = (v >> 1) as $i;
            //         if v & 1 != 0 {
            //             x = !x;
            //         }
            //         (x, n)
            //     })
            // }
        }
    )*)
}
impl_Varint!((u16, i16), (u32, i32), (u64, i64));

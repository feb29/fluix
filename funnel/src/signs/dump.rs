use super::{Sign, Signs};
use std::{borrow::Borrow, fmt, marker::PhantomData};

mod disp {
    pub trait Format {}
    pub struct Bin;
    pub struct Hex;
    impl Format for Bin {}
    impl Format for Hex {}
}

pub struct Dump<'a, S: 'a, F: disp::Format> {
    k: u64,
    signs: &'a Signs<S>,
    _fmt: PhantomData<F>,
}

impl<B: Borrow<Signs<S>>, S> Sign<B, S> {
    pub fn bin_dump(&self) -> Dump<S, disp::Bin> {
        let k = self.k;
        let signs = self.signs.borrow();
        let _fmt = PhantomData;
        Dump { k, signs, _fmt }
    }

    pub fn hex_dump(&self) -> Dump<S, disp::Hex> {
        let k = self.k;
        let signs = self.signs.borrow();
        let _fmt = PhantomData;
        Dump { k, signs, _fmt }
    }
}

macro_rules! fmtdebug {
    ($signs:expr, $k:expr, $f:expr, $p:expr, $rev:expr) => {{
        let mut n: u8 = 0;

        write!($f, "k:0x{:08X}", $k)?;
        macro_rules! putn {
            ($p2: expr) => {
                if $rev {
                    write!($f, $p2, reverse_bits(n) as u8)?;
                } else {
                    write!($f, $p2, n)?;
                }
            };
        }

        for (i, sign) in $signs.signs.iter().enumerate() {
            if sign.get($k) {
                n |= 1 << (i % 8);
            }

            if i % 8 == 7 {
                putn!(concat!(" ", $p));
                n = 0;
            }
        }
        putn!(concat!(" ", $p));
        Ok(())
    }};
}

fn reverse_bits<T: Into<u64>>(n: T) -> u64 {
    // https://graphics.stanford.edu/~seander/bithacks.html
    // use `reverse_bits` when the method is stabled.
    let n = n.into();
    ((n * 0x0002_0202_0202_u64) & 0x0108_8442_2010_u64) % 1023
}

#[test]
fn test_reverse_bits() {
    assert_eq!(0b00000000, reverse_bits(0b00000000_u8) as u8);
    assert_eq!(0b10000000, reverse_bits(0b00000001_u8) as u8);
    assert_eq!(0b10010100, reverse_bits(0b00101001_u8) as u8);
    assert_eq!(0b10010111, reverse_bits(0b11101001_u8) as u8);
    assert_eq!(0b11111111, reverse_bits(0b11111111_u8) as u8);
}

impl<'a, S: 'a> fmt::Debug for Dump<'a, S, disp::Bin> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmtdebug!(self.signs, self.k, f, "{:08b}", true)
    }
}

impl<'a, S: 'a> fmt::Debug for Dump<'a, S, disp::Hex> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmtdebug!(self.signs, self.k, f, "{:02x}", false)
    }
}

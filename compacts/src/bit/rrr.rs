use crate::num::{cast, Word};

// It is a good idea to choose `BLOCK_SIZE + 1` as a power of two,
// so that the bit that has size `CLASS_SIZE` can be fully used for bitpacking.
// e.g) 255: 8, 127: 7, 63: 6, 31: 5, 15: 4,
include!(concat!(env!("OUT_DIR"), "/table.rs"));

pub trait Code: Word {
    /// The minimum bit size to represents class value.
    const CLASS: usize;

    /// The bit size of code.
    const CODE_SIZE: usize = (Self::SIZE - 1) as usize;

    /// `MASK` is used to disable MSB (most significant bit).
    const MASK: Self;
}

macro_rules! implCode {
    ($(($type:ty, $class_size:expr)),*) => ($(
        impl Code for $type {
            const CLASS: usize = $class_size;
            const MASK: Self = (1 << Self::CODE_SIZE) - 1;
        }
    )*)
}

implCode!((u8, 3), (u16, 4), (u32, 5), (u64, 6), (u128, 7));

#[cfg(target_pointer_width = "32")]
implCode!((usize, 5));
#[cfg(target_pointer_width = "64")]
implCode!((usize, 6));

pub fn encode<C: Code>(code: C) -> (u64, C) {
    let code = code & C::MASK;

    let class = code.count1();
    let offset = {
        let mut c = cast::<u64, usize>(class);
        let mut o = 0;
        let mut j = 1;

        while 0 < c && c <= C::CODE_SIZE - j {
            if code.bit(cast(C::CODE_SIZE - j)) {
                o += TABLE[C::CODE_SIZE - j][c];
                c -= 1;
            }
            j += 1;
        }
        cast(o)
    };

    (class, offset)
}

pub fn decode<C: Code>(class: u64, offset: C) -> C {
    let mut code = C::MIN;
    let mut c = cast::<u64, usize>(class);
    let mut o = offset;
    let mut j = 1usize;

    while c > 0 {
        if o >= cast(TABLE[C::CODE_SIZE - j][c]) {
            code.set1(cast::<usize, u64>(C::CODE_SIZE - j));
            o -= cast::<u128, C>(TABLE[C::CODE_SIZE - j][c]);
            c -= 1;
        }
        j += 1;
    }
    code
}

// quickcheck! {
//     fn rrr8(code: u8) -> bool {
//         let (class, offset) = rrr::encode(code);
//         let got = rrr::decode(class, offset);
//         got == code & u8::MASK
//     }
//
//     fn rrr16(code: u16) -> bool {
//         let (class, offset) = rrr::encode(code);
//         let got = rrr::decode(class, offset);
//         got == code & u16::MASK
//     }
//
//     fn rrr32(code: u32) -> bool {
//         let (class, offset) = rrr::encode(code);
//         let got = rrr::decode(class, offset);
//         got == code & u32::MASK
//     }
//
//     fn rrr64(code: u64) -> bool {
//         let (class, offset) = rrr::encode(code);
//         let got = rrr::decode(class, offset);
//         got == code & u64::MASK
//     }
//
//     fn rrrsize(code: usize) -> bool {
//         let (class, offset) = rrr::encode(code);
//         let got = rrr::decode(class, offset);
//         got == code & usize::MASK
//     }
// }

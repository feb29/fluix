use crate::bits::*;

#[test]
fn set1_range() {
    let mut slice = [0b_00000000_u8, 0b_00000000, 0b_00000000];
    slice.set1(3..13);
    assert_eq!(slice, [0b_11111000_u8, 0b_00011111, 0b_00000000]);

    let mut slice = [0b_00000000_u8, 0b_00000000, 0b_00000000];
    slice.set1(1..4);
    assert_eq!(slice, [0b_00001110_u8, 0b_00000000, 0b_00000000]);
}

#[test]
fn set0_range() {
    let mut slice = [0b_11111000_u8, 0b_00011111, 0b_00000000];
    slice.set0(6..11);
    assert_eq!(slice, [0b_00111000u8, 0b_00011000, 0b_00000000]);

    let mut slice = [0b_11111000_u8, 0b_00011111, 0b_00000000];
    slice.set0(3..5);
    assert_eq!(slice, [0b_11100000_u8, 0b_00011111, 0b_00000000]);
}

quickcheck! {
    fn update_all(vec1: Vec<u64>, vec2: Vec<u64>) -> bool {
        let mut v1 = vec1;
        let mut v2 = vec2;
        let c1 = v1.count1();
        let r1 = c1 == v1.set0(..);

        let c0 = v2.count0();
        let r2 = c0 == v2.set1(..);

        r1 && r2
    }

    fn rank_select(vec: Vec<u64>) -> bool {
        dbg!(&vec);

        let mut bytes = Vec::<u8>::new();
        for &i in &vec {
            let k = i as usize / 8 ;
            if bytes.len() <= k {
                bytes.resize(k + 1, 0);
            }
            bytes.set1(i);
        }

        let mut entries = PageMap::<usize, u8>::new();
        for &i in &vec {
            entries.set1(i);
        }

        dbg!(&bytes);
        dbg!(&entries);

        let a = (0..bytes.count1()).take(1000).all(|i| {
            bytes.rank1(bytes.select1(i).unwrap()) == i
        });
        let b = (0..bytes.count0()).take(1000).all(|i| {
            bytes.rank0(bytes.select0(i).unwrap()) == i
        });

        let c = (0..entries.count1()).take(1000).all(|i| {
            entries.rank1(entries.select1(i).unwrap()) == i
        });
        let d = (0..entries.count0()).take(1000).all(|i| {
            entries.rank0(entries.select0(i).unwrap()) == i
        });

        a && b && c && d
    }

    fn search_select(vec: Vec<u64>) -> bool {
        (0..vec.count1()).all(|i| {
            vec.search1(i) == vec.select1(i)
        })
    }
}

#[test]
fn default_value() {
    let zero = <u64 as UnsignedInt>::ZERO;
    assert_eq!(zero, <u64 as Default>::default());
}

macro_rules! gen {
    ($Type:ty, $NBITS:expr, $BOUND:expr) => {
        use super::*;
        use crate::bits::*;
        use rand::prelude::*;

        type Type = $Type;

        macro_rules! bits {
            ($rng: expr) => {{
                let mut bits = Type::new();
                for _ in 0..$NBITS {
                    bits.set1($rng.gen_range(0, $BOUND));
                }
                bits
            }};
        }

        lazy_static! {
            static ref V0: Type = bits!(rng());
            static ref V1: Type = bits!(rng());
            static ref V2: Type = bits!(rng());
        }

        fn rng() -> ThreadRng {
            rand::thread_rng()
        }

        macro_rules! associative {
            ($x: expr,$y: expr,$z: expr,$fn: ident) => {{
                let r1 = $x.$fn($y).$fn($z).into_iter().collect::<PageMap<u64, Array>>();
                let r2 = $x.$fn($y.$fn($z)).into_iter().collect::<PageMap<u64, Array>>();
                r1 == r2
            }};
        }

        macro_rules! commutative {
            ($x: expr,$y: expr,$fn: ident) => {{
                let r1 = $x.$fn($y).into_iter().collect::<PageMap<u64, Array>>();
                let r2 = $y.$fn($x).into_iter().collect::<PageMap<u64, Array>>();
                r1 == r2
            }};
        }

        #[test]
        fn associative() {
            assert!(associative!(&*V0, &*V1, &*V2, and));
            assert!(associative!(&*V0, &*V1, &*V2, or));
            assert!(associative!(&*V0, &*V1, &*V2, xor));
        }

        #[test]
        fn commutative() {
            assert!(commutative!(&*V0, &*V1, and));
            assert!(commutative!(&*V1, &*V2, and));
            assert!(commutative!(&*V0, &*V2, and));

            assert!(commutative!(&*V0, &*V1, or));
            assert!(commutative!(&*V1, &*V2, or));
            assert!(commutative!(&*V0, &*V2, or));

            assert!(commutative!(&*V0, &*V1, xor));
            assert!(commutative!(&*V1, &*V2, xor));
            assert!(commutative!(&*V0, &*V2, xor));
        }

        fn from_bits(data: &[u64]) -> $Type {
            let mut bv: $Type = Default::default();
            for &i in data.as_ref() {
                bv.set1(i);
            }
            bv
        }

        quickcheck! {
            fn quickcheck_associative(vec1: Vec<u64>, vec2: Vec<u64>, vec3: Vec<u64>) -> bool {
                let b1 = &from_bits(&vec1[..]);
                let b2 = &from_bits(&vec2[..]);
                let b3 = &from_bits(&vec3[..]);
                associative!(b1, b2, b3, and) && associative!(b1, b2, b3, or) && associative!(b1, b2, b3, xor)
            }

            fn quickcheck_commutative(vec1: Vec<u64>, vec2: Vec<u64>) -> bool {
                let b1 = &from_bits(&vec1[..]);
                let b2 = &from_bits(&vec2[..]);
                commutative!(b1, b2, and) && commutative!(b1, b2, or) && commutative!(b1, b2, xor)
            }
        }
    };
}

mod array {
    const BITSIZE: u64 = 010_000_000;

    mod density_00 {
        gen!(PageMap<u64, Array>, BITSIZE/1000, BITSIZE);
    }
    mod density_05 {
        gen!(PageMap<u64, Array>, BITSIZE/20, BITSIZE);
    }
    mod density_10 {
        gen!(PageMap<u64, Array>, BITSIZE/10, BITSIZE);
    }
    mod density_20 {
        gen!(PageMap<u64, Array>, BITSIZE/5, BITSIZE);
    }
    mod density_50 {
        gen!(PageMap<u64, Array>, BITSIZE/2, BITSIZE);
    }
}

mod block {
    const BITSIZE: u64 = 010_000_000;

    mod density_00 {
        gen!(PageMap<u64, RoaringBlock>, BITSIZE/1000, BITSIZE);
    }
    mod density_05 {
        gen!(PageMap<u64, RoaringBlock>, BITSIZE/20, BITSIZE);
    }
    mod density_10 {
        gen!(PageMap<u64, RoaringBlock>, BITSIZE/10, BITSIZE);
    }
    mod density_20 {
        gen!(PageMap<u64, RoaringBlock>, BITSIZE/5, BITSIZE);
    }
    mod density_50 {
        gen!(PageMap<u64, RoaringBlock>, BITSIZE/2, BITSIZE);
    }
}

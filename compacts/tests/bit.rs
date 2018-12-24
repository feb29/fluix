use compacts::{bit::ops::*, bit::*};
use lazy_static::lazy_static;
use quickcheck::quickcheck;
use rand::prelude::*;

quickcheck! {
    // fn bits(vec: Vec<u64>) -> bool {
    //     vec.ones().take(1000).all(|i| {
    //         vec.bits::<u8>(i, 1) == 1
    //     })
    // }

    fn put1(vec: Vec<u64>) -> bool {
        let mut vec = vec;
        (0..vec.size()).all(|i| {
            let n = vec.put1(i);
            n == 1 || n == 0
        })
    }
    fn put0(vec: Vec<u64>) -> bool {
        let mut vec = vec;
        (0..vec.size()).all(|i| {
            let n = vec.put0(i);
            n == 1 || n == 0
        })
    }

    fn flip(vec1: Vec<u64>, vec2: Vec<u64>) -> bool {
        let mut v1 = vec1;
        let mut v2 = vec2;

        let r1 = {
            let c1 = v1.count1();
            v1.flip(..);
            c1 == v1.count0()
        };

        let r2 = {
            let c0 = v2.count0();
            v2.flip(..);
            c0 == v2.count1()
        };

        r1 && r2
    }

    fn dict(vec: Vec<u64>) -> bool {
        let a = (0..vec.count1()).take(1000).all(|i| {
            vec.rank1(vec.select1(i).unwrap()) == i
        });
        let b = (0..vec.count0()).take(1000).all(|i| {
            vec.rank0(vec.select0(i).unwrap()) == i
        });
        a && b
    }
}

macro_rules! associative {
    ($x: expr,$y: expr,$z: expr,$fn: ident) => {{
        let r1 = $fn($fn($x, $y), $z).into_iter().collect::<Map<u64>>();
        let r2 = $fn($x, $fn($y, $z)).into_iter().collect::<Map<u64>>();
        r1 == r2
    }};
}

macro_rules! commutative {
    ($x: expr,$y: expr,$fn: ident) => {{
        let r1 = $fn($x, $y).into_iter().collect::<Map<u64>>();
        let r2 = $fn($y, $x).into_iter().collect::<Map<u64>>();
        r1 == r2
    }};
}

fn bits<R: Rng>(mut rng: R, nsize: u64, bound: u64) -> Vec<u64> {
    let mut vec = Vec::new();
    for _ in 0..nsize {
        vec.push(rng.gen_range(0, bound));
    }
    vec.dedup();
    vec.sort_unstable();
    vec
}

macro_rules! init_data {
    ($build:ident, $bits:expr, $BOUND:expr) => {{
        let mut repr = $build($BOUND);
        for &b in $bits {
            repr.put1(b);
        }
        repr
    }};
}

macro_rules! test {
    ($build:ident, $Repr:ty, $Block:ty) => {
        use super::*;

        lazy_static! {
            static ref NSIZE: u64 = BOUND / thread_rng().gen_range(1, 100);
            static ref BITS0: Vec<u64> = bits(thread_rng(), *NSIZE, BOUND);
            static ref BITS1: Vec<u64> = bits(thread_rng(), *NSIZE, BOUND);
            static ref BITS2: Vec<u64> = bits(thread_rng(), *NSIZE, BOUND);
        }

        lazy_static! {
            static ref V0: $Repr = init_data!($build, &*BITS0, BOUND);
            static ref V1: $Repr = init_data!($build, &*BITS1, BOUND);
            static ref V2: $Repr = init_data!($build, &*BITS2, BOUND);
        }

        lazy_static! {
            static ref A0: Array<$Block> = Array::from(V0.clone());
            static ref A1: Array<$Block> = Array::from(V1.clone());
            static ref A2: Array<$Block> = Array::from(V2.clone());
        }

        mod array {
            use super::*;
            #[test]
            fn rank1_sum() {
                dbg!(A0.size());
                let i = dbg!(A0.size() / 3 * 1);
                let j = dbg!(A0.size() / 3 * 2);
                assert_eq!(A0.rank1(..), A0.count1());
                assert_eq!(A0.rank1(..i) + A0.rank1(i..j) + A0.rank1(j..), A0.count1());
            }
        }

        mod prop {
            use super::*;
            #[test]
            fn rank1_sum() {
                let i = V0.size() / 3 * 1;
                let j = V0.size() / 3 * 2;
                assert_eq!(V0.rank1(..), V0.count1());
                assert_eq!(V0.rank1(..i) + V0.rank1(i..j) + V0.rank1(j..), V0.count1());
            }
        }

        mod fold {
            use super::*;
            #[test]
            fn and() {
                let map1 = Fold::and(vec![&*V0, &*V1, &*V2]).collect::<Map<u64>>();
                let map2 = V0.and(&*V1).and(&*V2).into_steps().collect::<Map<u64>>();
                assert_eq!(map1, map2);
            }

            #[test]
            fn or() {
                let map1 = Fold::or(vec![&*V0, &*V1, &*V2]).collect::<Map<u64>>();
                let map2 = V0.or(&*V1).or(&*V2).into_steps().collect::<Map<u64>>();
                assert_eq!(map1, map2);
            }

            #[test]
            fn xor() {
                let map1 = Fold::xor(vec![&*V0, &*V1, &*V2]).collect::<Map<u64>>();
                let map2 = V0.xor(&*V1).xor(&*V2).into_steps().collect::<Map<u64>>();
                assert_eq!(map1, map2);
            }
        }

        mod bitwise {
            use super::*;

            #[test]
            fn associative_and() {
                assert!(associative!(&*V0, &*V1, &*V2, and), "and");
            }
            #[test]
            fn associative_or() {
                assert!(associative!(&*V0, &*V1, &*V2, or), "or");
            }
            #[test]
            fn associative_xor() {
                assert!(associative!(&*V0, &*V1, &*V2, xor), "xor");
            }

            #[test]
            fn commutative_and() {
                assert!(commutative!(&*V0, &*V1, and), "V0 & V1");
                assert!(commutative!(&*V1, &*V2, and), "V1 & V2");
                assert!(commutative!(&*V0, &*V2, and), "V0 & V2");
            }

            #[test]
            fn commutative_or() {
                assert!(commutative!(&*V0, &*V1, or), "V0 | V1");
                assert!(commutative!(&*V1, &*V2, or), "V1 | V2");
                assert!(commutative!(&*V0, &*V2, or), "V0 | V2");
            }

            #[test]
            fn commutative_xor() {
                assert!(commutative!(&*V0, &*V1, xor), "V0 ^ V1");
                assert!(commutative!(&*V1, &*V2, xor), "V1 ^ V2");
                assert!(commutative!(&*V0, &*V2, xor), "V0 ^ V2");
            }
        }

        #[test]
        fn rank_select() {
            for _ in 0..1000 {
                let rank1 = thread_rng().gen_range(0, V0.count1());
                assert!(V0.rank1(V0.select1(rank1).unwrap()) == rank1);
                let rank0 = thread_rng().gen_range(0, V0.count0());
                assert!(V0.rank0(V0.select0(rank0).unwrap()) == rank0);
            }
        }

        #[test]
        fn array_rank_select() {
            let cs = Array::from(V0.clone());
            for _ in 0..1000 {
                let rank1 = thread_rng().gen_range(0, cs.count1());
                assert!(cs.rank1(cs.select1(rank1).unwrap()) == rank1);
                let rank0 = thread_rng().gen_range(0, cs.count0());
                assert!(cs.rank0(cs.select0(rank0).unwrap()) == rank0);
            }
        }
    };
}

macro_rules! genmods {
    ($BOUND:expr) => {
        use super::*;
        const BOUND: u64 = $BOUND;

        mod vec_naive {
            test!(build_vec, Vec<u64>, u64);
        }
        mod vec_block {
            test!(build_vec, Vec<Block>, Block);
        }
        mod map_usize {
            test!(build_map, Map<usize>, Block);
        }
    };
}

fn build_vec<X: Bits>(bound: u64) -> Vec<X> {
    sized(bound)
}
fn build_map<X: Bit>(_bound: u64) -> Map<X> {
    Map::<X>::default()
}

mod size_001m {
    genmods!(1_000_000);
}
mod size_010m {
    genmods!(10_000_000);
}

#![feature(test)]
extern crate test;

use compacts::{bit, bit::ops::*, bit::*};
use lazy_static::lazy_static;
use rand::prelude::*;
use test::Bencher;

macro_rules! bench {
    ($gen:expr, $Type:ty, $Block:ty, $NSIZE:expr, $BOUND:expr) => {
        use super::*;

        type Type = $Type;

        lazy_static! {
            static ref ARRAY: Array<$Block> = Array::from(V0.clone());
            static ref TABLE: Vec<Type> = {
                let mut rng = rng();
                vec![
                    $gen(&mut rng, $NSIZE, $BOUND),
                    $gen(&mut rng, $NSIZE, $BOUND),
                    $gen(&mut rng, $NSIZE, $BOUND),
                ]
            };
            static ref V0: &'static Type = &TABLE[0];
            static ref V1: &'static Type = &TABLE[1];
            static ref V2: &'static Type = &TABLE[2];
        }

        fn rng() -> ThreadRng {
            rand::thread_rng()
        }

        mod ops {
            use super::*;
            #[bench]
            fn bit(bench: &mut Bencher) {
                bench.iter(|| V0.bit(std::cmp::min($BOUND, rng().gen())));
            }

            #[bench]
            fn put1(bench: &mut Bencher) {
                let mut b = V0.clone();
                bench.iter(|| b.put1(std::cmp::min($BOUND, rng().gen())));
            }

            #[bench]
            fn put0(bench: &mut Bencher) {
                let mut b = V0.clone();
                bench.iter(|| b.put0(std::cmp::min($BOUND, rng().gen())));
            }

            #[bench]
            fn puts(bench: &mut Bencher) {
                let mut b = V0.clone();
                bench.iter(|| b.puts(std::cmp::min($BOUND, rng().gen()), 8, !0u64));
            }

            #[bench]
            fn rank1(bench: &mut Bencher) {
                bench.iter(|| V0.rank1(rng().gen_range(0, V0.size())));
            }

            #[bench]
            fn select1(bench: &mut Bencher) {
                bench.iter(|| V0.select1(rng().gen_range(0, V0.count1() / 2)));
            }

            #[bench]
            fn search1(bench: &mut Bencher) {
                bench.iter(|| V0.search1(rng().gen_range(0, V0.count1() / 2)));
            }
        }

        mod array {
            use super::*;

            #[bench]
            fn build(bench: &mut Bencher) {
                bench.iter(|| Array::from(V0.clone()))
            }

            #[bench]
            fn rank1(bench: &mut Bencher) {
                let a = Array::from(V0.clone());
                // bench.iter(|| ARRAY.rank1(rng().gen_range(0, ARRAY.size())));
                bench.iter(|| a.rank1(rng().gen_range(0, a.size())));
            }
            #[bench]
            fn select1(bench: &mut Bencher) {
                let a = Array::from(V0.clone());
                // bench.iter(|| ARRAY.select1(rng().gen_range(0, ARRAY.count1() - 1)));
                bench.iter(|| a.select1(rng().gen_range(0, a.count1() - 1)));
            }
        }

        mod bitwise {
            use super::*;

            #[bench]
            fn and(bench: &mut Bencher) {
                bench.iter(|| V0.and(*V1).and(*V2).into_iter().collect::<Map<u64>>());
            }

            #[bench]
            fn or(bench: &mut Bencher) {
                bench.iter(|| V0.or(*V1).or(*V2).into_iter().collect::<Map<u64>>());
            }

            #[bench]
            fn xor(bench: &mut Bencher) {
                bench.iter(|| V0.xor(*V1).xor(*V2).into_iter().collect::<Map<u64>>());
            }
        }

        mod fold {
            use super::*;

            #[bench]
            fn and(bench: &mut Bencher) {
                bench.iter(|| Fold::and(&*TABLE).into_iter().collect::<Map<u64>>());
            }

            #[bench]
            fn or(bench: &mut Bencher) {
                bench.iter(|| Fold::or(&*TABLE).into_iter().collect::<Map<u64>>());
            }

            #[bench]
            fn xor(bench: &mut Bencher) {
                bench.iter(|| Fold::xor(&*TABLE).into_iter().collect::<Map<u64>>());
            }
        }
    };
}

fn rand_vec<R: Rng, X: Bits>(mut rng: R, nsize: usize, bound: u64) -> Vec<X> {
    let mut bit_vec = bit::sized(bound);
    for _ in 0..nsize {
        bit_vec.put1(rng.gen_range(0, bound));
    }
    bit_vec
}
fn rand_map<R: Rng, X: Bit>(mut rng: R, nsize: usize, bound: u64) -> Map<X> {
    let mut bit_vec = Map::default();
    for _ in 0..nsize {
        bit_vec.put1(rng.gen_range(0, bound));
    }
    bit_vec
}

macro_rules! genmods {
    ($BOUND:expr) => {
        use super::*;

        mod vec_naive_01 {
            bench!(rand_vec, Vec<u64>, u64, $BOUND / 100, $BOUND);
        }
        mod vec_naive_10 {
            bench!(rand_vec, Vec<u64>, u64, $BOUND / 10, $BOUND);
        }
        mod vec_naive_50 {
            bench!(rand_vec, Vec<u64>, u64, $BOUND / 2, $BOUND);
        }

        mod vec_block_01 {
            bench!(rand_vec, Vec<Block>, Block, $BOUND / 100, $BOUND);
        }
        mod vec_block_10 {
            bench!(rand_vec, Vec<Block>, Block, $BOUND / 10, $BOUND);
        }
        mod vec_block_50 {
            bench!(rand_vec, Vec<Block>, Block, $BOUND / 2, $BOUND);
        }

        mod map_usize_01 {
            bench!(rand_map, Map<usize>, Block, $BOUND / 100, $BOUND);
        }
        mod map_usize_10 {
            bench!(rand_map, Map<usize>, Block, $BOUND / 10, $BOUND);
        }
        mod map_usize_50 {
            bench!(rand_map, Map<usize>, Block, $BOUND / 2, $BOUND);
        }
    };
}

mod size_001m {
    genmods!(1_000_000);
}

mod size_010m {
    genmods!(10_000_000);
}

// mod size_300m {
//     genmods!(300_000_000);
// }

// mod size_3b {
//     genmods!(3_000_000_000);
// }

// mod size_xl {
//     genmods!(1 << 32);
// }

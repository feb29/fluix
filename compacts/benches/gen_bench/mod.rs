macro_rules! gen_bench {
    ($Type:tt, $Words:ty, $NBITS:expr, $BOUND:expr) => {
        use compacts::bit_set::{self, BitSet};

        use {rand, rand::prelude::*, test::Bencher};

        type Ty = $Words;
        type BitSetType = $Type<Ty>;

        macro_rules! bits {
            ($nbits: expr,$range: expr,$rng: expr) => {{
                let mut bits = BitSetType::new();
                for _ in 0..$nbits {
                    bits.insert($rng.gen_range($range.start, $range.end));
                }
                bits
            }};
        }

        lazy_static! {
            static ref XS: Vec<BitSetType> = {
                let mut vec = Vec::with_capacity(8);
                vec.push(bits!($NBITS, 0..$BOUND, rng()));
                vec.push(bits!($NBITS, 0..$BOUND, rng()));
                vec.push(bits!($NBITS, 0..$BOUND, rng()));
                vec.push(bits!($NBITS, 0..$BOUND, rng()));
                vec.push(bits!($NBITS, 0..$BOUND, rng()));
                vec.push(bits!($NBITS, 0..$BOUND, rng()));
                vec.push(bits!($NBITS, 0..$BOUND, rng()));
                vec.push(bits!($NBITS, 0..$BOUND, rng()));
                vec
            };
            static ref V0: &'static BitSetType = &XS[0];
            static ref V1: &'static BitSetType = &XS[1];
            static ref V2: &'static BitSetType = &XS[2];
            static ref V3: &'static BitSetType = &XS[3];
            static ref V4: &'static BitSetType = &XS[4];
            static ref V5: &'static BitSetType = &XS[5];
            static ref V6: &'static BitSetType = &XS[6];
            static ref V7: &'static BitSetType = &XS[7];
        }

        fn rng() -> ThreadRng {
            rand::thread_rng()
        }

        const SIZE: u64 = 1_000_000;

        #[bench]
        fn access(bench: &mut Bencher) {
            let bits = &*V0;
            bench.iter(|| bits.access(std::cmp::min(1 << 32, rng().gen())));
        }

        #[bench]
        fn insert(bench: &mut Bencher) {
            let mut bits = V0.clone();
            bench.iter(|| bits.insert(std::cmp::min(1 << 32, rng().gen())));
        }

        #[bench]
        fn remove(bench: &mut Bencher) {
            let mut bits = V0.clone();
            bench.iter(|| bits.remove(std::cmp::min(1 << 32, rng().gen())));
        }

        #[bench]
        fn rank1(bench: &mut Bencher) {
            bench.iter(|| V0.rank1(SIZE));
        }

        #[bench]
        fn select1(bench: &mut Bencher) {
            let max = V0.count1() - 1;
            bench.iter(|| V0.select1(std::cmp::min(SIZE, max)));
        }
        #[bench]
        fn select0(bench: &mut Bencher) {
            let max = V0.count0() - 1;
            bench.iter(|| V0.select0(std::cmp::min(SIZE, max)));
        }

        #[bench]
        fn and(bench: &mut Bencher) {
            bench.iter(|| V1.and(*V2).and(*V3).into_iter().collect::<BitSetType>());
        }

        #[bench]
        fn and_slice(bench: &mut Bencher) {
            bench.iter(|| {
                let slice = V1.get(..SIZE);
                slice
                    .and(V2.get(..SIZE))
                    .and(V3.get(..SIZE))
                    .into_iter()
                    .collect::<BitSetType>()
            });
        }

        #[bench]
        fn or(bench: &mut Bencher) {
            bench.iter(|| V1.or(*V2).or(*V3).into_iter().collect::<BitSetType>());
        }

        #[bench]
        fn xor(bench: &mut Bencher) {
            bench.iter(|| V1.xor(*V2).xor(*V3).into_iter().collect::<BitSetType>());
        }

        #[bench]
        fn and_not(bench: &mut Bencher) {
            bench.iter(|| {
                V1.and(V2.not())
                    .and(V3.not())
                    .into_iter()
                    .collect::<BitSetType>()
            });
        }

        #[bench]
        fn fold_and(bench: &mut Bencher) {
            bench.iter(|| bit_set::Fold::and(&*XS).into_iter().collect::<BitSetType>());
        }

        #[bench]
        fn fold_or(bench: &mut Bencher) {
            bench.iter(|| bit_set::Fold::or(&*XS).into_iter().collect::<BitSetType>());
        }

        #[bench]
        fn fold_xor(bench: &mut Bencher) {
            bench.iter(|| bit_set::Fold::xor(&*XS).into_iter().collect::<BitSetType>());
        }

        #[bench]
        fn slice_fold_and(bench: &mut Bencher) {
            bench.iter(|| {
                bit_set::Fold::and(XS.iter().map(|bv| bv.get(..SIZE)))
                    .into_iter()
                    .collect::<BitSetType>()
            });
        }

        #[bench]
        fn slice_fold_or(bench: &mut Bencher) {
            bench.iter(|| {
                bit_set::Fold::or(XS.iter().map(|bv| bv.get(..SIZE)))
                    .into_iter()
                    .collect::<BitSetType>()
            });
        }

        #[bench]
        fn slice_fold_xor(bench: &mut Bencher) {
            bench.iter(|| {
                bit_set::Fold::xor(XS.iter().map(|bv| bv.get(..SIZE)))
                    .into_iter()
                    .collect::<BitSetType>()
            });
        }
    };
}

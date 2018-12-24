use crate::{
    bit::ops::*,
    bit::{self, Bit, Block, Encode, Map},
    num::{cast, divrem, search_index, Word},
};

/// An immutable and uncompressed bit sequence with the index for Rank and Select1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Array<T> {
    // the number of enabled bit
    ones: u64,
    // original bit vector
    data: Vec<T>,
    // L0: cumulative     absolute counts
    // L1: cumulative     relative counts
    // L2: non-cumulative relative counts
    l0s: Vec<u64>,
    // L1 and L2 are interleaved into one vector,
    // each L1 entries is followed by its L2 index entries.
    l1l2s: Vec<L1L2>,
    // sampling answers for select1
    samples: Samples,
}

const UPPER_BLOCK: u64 = 1 << 32;
const SUPER_BLOCK: u64 = 2048;
const BASIC_BLOCK: u64 = 512;

const NUM_SB: usize = (1 << 32) / 2048; // 2097152
const NUM_BB: usize = 2048 / 512;

// SuperBlock holds the number of '1' per BASIC_BLOCK
type SuperBlock = [u64; NUM_BB];

impl<T: Bits> BitCount for Array<T> {
    #[inline(always)]
    fn size(&self) -> u64 {
        self.data.size()
    }
    #[inline(always)]
    fn count1(&self) -> u64 {
        self.ones
    }
}

impl<T: Bits> BitGet for Array<T> {
    #[inline(always)]
    fn bits<W: Word>(&self, i: u64, n: u64) -> W {
        self.data.bits(i, n)
    }
    #[inline(always)]
    fn bit(&self, i: u64) -> bool {
        self.data.bit(i)
    }
    #[inline(always)]
    fn ones<'a>(&'a self) -> Box<dyn Iterator<Item = u64> + 'a> {
        self.data.ones()
    }
}

impl<T: Bits> Array<T> {
    #[inline]
    fn rank(&self, p0: u64) -> u64 {
        assert!(p0 <= self.size());
        if p0 == self.size() {
            return self.count1();
        }
        // p0 < self.size()
        let mut rank = self.l0s[cast::<u64, usize>(p0 / UPPER_BLOCK)];
        let (q1, r1) = divrem::<usize>(p0, SUPER_BLOCK);
        let (q2, r2) = divrem::<usize>(r1, BASIC_BLOCK);
        let l1l2 = self.l1l2s[q1];
        rank += l1l2.l1();
        rank += l1l2.l2(q2);
        rank += self.data.rank1(p0 - r2..p0);
        rank
    }
}

impl<T: Bits> BitRank for Array<T> {
    #[inline]
    fn rank1<Ix: IntoBounds>(&self, b: Ix) -> u64 {
        match b.into_bounds(self.size()) {
            Bounds(0, i) => self.rank(i),
            Bounds(i, j) => self.rank(j) - self.rank(i),
        }
    }
}

impl<T: Word> From<Vec<T>> for Array<T> {
    fn from(data: Vec<T>) -> Self {
        let (ones, l0s, l1l2s) = rank1_samples(data.size(), {
            let super_block_len = cast::<u64, usize>(SUPER_BLOCK / T::SIZE);
            data.chunks(super_block_len).map(|slice| {
                debug_assert!(slice.size() <= SUPER_BLOCK);
                let mut blocks = [0; NUM_BB];
                for (i, (n, len)) in bit::ix_len(0, slice.size(), BASIC_BLOCK).enumerate() {
                    blocks[i] = slice.rank1(n..n + len);
                }
                blocks
            })
        });
        debug_assert_eq!(ones, data.count1());

        let samples = select1_samples(l0s.len(), data.iter().enumerate().map(|(i, &w)| (i, w)));

        Array {
            ones,
            data,
            l0s,
            l1l2s,
            samples,
        }
    }
}

impl From<Vec<Block>> for Array<Block> {
    fn from(data: Vec<Block>) -> Self {
        let (ones, l0s, l1l2s) = {
            let size = data.size();
            let supers = data.iter().flat_map(|block| {
                let mut supers = vec![[0; NUM_BB]; (Block::SIZE / SUPER_BLOCK) as usize];
                if block.count1() > 0 {
                    for (i, (n, m)) in bit::ix_len(0, Block::SIZE, SUPER_BLOCK).enumerate() {
                        debug_assert_eq!(m, SUPER_BLOCK);
                        let mut blocks = [0; NUM_BB];
                        for (j, (x, y)) in bit::ix_len(n, n + m, BASIC_BLOCK).enumerate() {
                            debug_assert_eq!(y, BASIC_BLOCK);
                            blocks[j] = block.rank1(x..x + y);
                        }
                        supers[i] = blocks;
                    }
                }
                supers
            });
            rank1_samples(size, supers)
        };

        debug_assert_eq!(ones, data.count1());

        let samples = {
            let words = data.iter().enumerate().flat_map(|(i, block)| {
                let offset = i * Block::VEC_LEN;
                match block {
                    Block(Encode::Seq(seq)) => {
                        let iter: Box<dyn Iterator<Item = (usize, u64)>> =
                            Box::new(bit::ix_len(0, Block::SIZE, u64::SIZE).enumerate().map(
                                move |(j, (x, y))| {
                                    let index = offset + j;
                                    let bits = seq.bits::<u64>(x, y);
                                    (index, bits)
                                },
                            ));
                        iter
                    }
                    Block(Encode::Vec(vec)) => {
                        if let Some(slice) = vec.as_ref() {
                            let iter: Box<dyn Iterator<Item = (usize, u64)>> = Box::new(
                                slice
                                    .iter()
                                    .cloned()
                                    .enumerate()
                                    .map(move |(i, w)| (offset + i, w)),
                            );
                            iter
                        } else {
                            let iter: Box<dyn Iterator<Item = (usize, u64)>> = Box::new(
                                std::iter::repeat(0)
                                    .enumerate()
                                    .map(move |(i, w)| (offset + i, w))
                                    .take(Block::VEC_LEN),
                            );
                            iter
                        }
                    }
                }
            });
            select1_samples(l0s.len(), words)
        };

        Array {
            ones,
            data,
            l0s,
            l1l2s,
            samples,
        }
    }
}

impl<T: Bit> From<Map<T>> for Array<Block> {
    fn from(map: Map<T>) -> Self {
        Self::from(map.into_vec())
    }
}

fn rank1_samples(n: u64, sups: impl Iterator<Item = SuperBlock>) -> (u64, Vec<u64>, Vec<L1L2>) {
    let mut cur = 0;
    let mut pre = 0;

    let mut l0s = vec![0; cast(n / UPPER_BLOCK + 1)];
    let mut l1l2s = vec![L1L2(0); cast(n / SUPER_BLOCK + 1)];

    for (i, l2) in sups.enumerate() {
        if i % NUM_SB == 0 {
            l0s[i / NUM_SB] = cur;
            pre = cur;
        }
        let l1 = cur - pre;
        l1l2s[i] = L1L2::interleave(l1, l2[0], l2[1], l2[2]);
        cur += l2[0] + l2[1] + l2[2] + l2[3];
    }
    (cur, l0s, l1l2s)
}

fn select1_samples<T: Word>(len: usize, words: impl Iterator<Item = (usize, T)>) -> Samples {
    const USIZE: u64 = 8192;
    const ISIZE: i64 = 8192;
    let numw = UPPER_BLOCK / T::SIZE;
    let mut vecs = vec![Vec::new(); len]; // UPPER_BLOCKs
    let mut ones = 0i64; // max is 1<<63
    for (i, w) in words {
        let sample_index = i / cast::<u64, usize>(numw);
        let select_index = ((-ones) % ISIZE + ISIZE) % ISIZE; // modulo, not remainder
        let pop_count = w.count1();

        if (select_index as u64) < pop_count {
            let select = w.select1(select_index as u64).unwrap();
            let x = i as u64 * T::SIZE + select - (sample_index as u64) * UPPER_BLOCK;
            vecs[sample_index].push(x as u32);
        }

        if (i as u64) % numw == numw - 1 {
            ones = 0;
        } else {
            ones += pop_count as i64;
        }
    }

    Samples { size: USIZE, vecs }
}

// interleaved value of L1[i] and L2[i]
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct L1L2(u64);

#[allow(clippy::large_digit_groups)]
impl L1L2 {
    fn interleave(mut l1: u64, l2_0: u64, l2_1: u64, l2_2: u64) -> Self {
        assert!(l1 < UPPER_BLOCK && l2_0 < 1024 && l2_1 < 1024 && l2_2 < 1024);
        l1 |= l2_0 << 32;
        l1 |= l2_1 << 42;
        l1 |= l2_2 << 52;
        L1L2(l1)
    }

    #[inline(always)]
    fn l1(self) -> u64 {
        (self.0 & 0b_00000000000000000000000000000000_11111111111111111111111111111111_u64)
    }

    fn l2(self, index: usize) -> u64 {
        match index {
            0 => 0,
            1 => self.l2_0(),
            2 => self.l2_0() + self.l2_1(),
            3 => self.l2_0() + self.l2_1() + self.l2_2(),
            _ => unreachable!("basic block: index out of bounds"),
        }
    }

    #[inline(always)]
    fn l2_0(self) -> u64 {
        (self.0 & 0b_00000000000000000000001111111111_00000000000000000000000000000000_u64) >> 32
    }
    #[inline(always)]
    fn l2_1(self) -> u64 {
        (self.0 & 0b_00000000000011111111110000000000_00000000000000000000000000000000_u64) >> 42
    }
    #[inline(always)]
    fn l2_2(self) -> u64 {
        (self.0 & 0b_00111111111100000000000000000000_00000000000000000000000000000000_u64) >> 52
    }
}

// Sampling answers for `Select1/Select0`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Samples {
    size: u64,
    vecs: Vec<Vec<u32>>,
}

impl<T: Bits> BitSelect1 for Array<T> {
    fn select1(&self, nth: u64) -> Option<u64> {
        if nth >= self.count1() {
            return None;
        };

        // Lookup in L0 to find the right UpperBlock
        let l0_index = search_index(0, self.l0s.len(), |k| nth < self.l0s[k]) - 1;
        let mut remain = nth - self.l0s[l0_index];

        // Lookup in sampling answers to find the nearby LowerBlock
        let (n, m) = {
            let samples = &self.samples.vecs[l0_index];
            let skipped = cast::<usize, u64>(l0_index) * UPPER_BLOCK;
            let i = cast::<u64, usize>(remain / self.samples.size);
            let j = i + 1;
            let min = samples.get(i).map_or(0, |&k| cast::<u32, u64>(k));
            let max = samples.get(j).map_or(UPPER_BLOCK, |&k| cast::<u32, u64>(k));
            assert!(min < max);
            (
                (skipped + min) / SUPER_BLOCK,
                (skipped + max) / SUPER_BLOCK + 1,
            )
        };

        let (l1l2_index, l2_index) = {
            // Lookup in L1 to find the right LowerBlock
            let i = std::cmp::min(cast(n), self.l1l2s.len() - 1);
            let j = std::cmp::min(cast(m), self.l1l2s.len());
            let l1l2_index = search_index(i, j, |k| remain < self.l1l2s[k].l1()) - 1;

            let l1l2 = self.l1l2s[l1l2_index];
            let l1 = l1l2.l1();
            let l2 = [l1l2.l2_0(), l1l2.l2_1(), l1l2.l2_2()];

            assert!(remain >= l1);
            remain -= l1;

            // Lookup in L2 to find the right BasicBlock
            let l2_index = {
                let mut index = 0;
                for &l2 in l2.iter() {
                    if remain < l2 {
                        break;
                    }
                    remain -= l2;
                    index += 1;
                }
                index
            };
            (l1l2_index, l2_index)
        };

        let mut pos = {
            let sb = cast::<usize, u64>(l1l2_index) * SUPER_BLOCK;
            let bb = cast::<usize, u64>(l2_index) * BASIC_BLOCK;
            sb + bb
        };

        assert!(remain <= 512);
        loop {
            let w = self.data.bits::<u64>(pos, u64::SIZE);
            let c = w.count1();
            if remain < c {
                pos += w.select1(remain).unwrap();
                break;
            }
            pos += u64::SIZE;
            remain -= c;
        }

        Some(pos)
    }
}

impl<T: Bits> BitSelect0 for Array<T> {
    #[inline]
    fn select0(&self, n: u64) -> Option<u64> {
        self.search0(n)
    }
}

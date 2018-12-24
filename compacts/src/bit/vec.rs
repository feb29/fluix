use std::{borrow::Cow, iter::Enumerate};

use crate::{
    bit::{ops::*, Block, IntoSteps, Slice, Step, BLOCK_SIZE, OUT_OF_BOUNDS},
    num::{cast, divrem, Word},
};

impl<T: Bits> BitCount for [T] {
    /// ```
    /// use compacts::bit::ops::BitCount;
    /// let vec = vec![0u64, 0b10101100000, 0b0000100000];
    /// assert_eq!(vec.size(), 64*3);
    /// assert_eq!(vec.count1(), 5);
    /// ```
    fn size(&self) -> u64 {
        cast::<usize, u64>(self.len()) * T::SIZE
    }
    fn count1(&self) -> u64 {
        self.iter().fold(0, |acc, w| acc + w.count1())
    }
}

impl<T: Bits> BitGet for [T] {
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::{self, Block, ops::{BitGet, BitPut}};
    /// let mut vec: Vec<Block> = bit::sized(131071);
    /// for &b in &[65534, 65535, 65536, 65537, 131071] {
    ///     vec.put1(b);
    /// }
    /// assert_eq!(vec.bits::<u64>(     0, 64), 0b_0000_0000);
    /// assert_eq!(vec.bits::<u64>(    64, 64), 0b_0000_0000);
    /// assert_eq!(vec.bits::<u64>( 65530, 60), 0b_1111_0000);
    /// assert_eq!(vec.bits::<u64>( 65534, 16), 0b_0000_1111);
    /// assert_eq!(vec.bits::<u64>( 65535, 63), 0b_0000_0111);
    /// assert_eq!(vec.bits::<u64>( 65536, 63), 0b_0000_0011);
    /// assert_eq!(vec.bits::<u64>(131071,  1), 0b_0000_0001); // size=131072
    /// ```
    fn bits<W: Word>(&self, i: u64, len: u64) -> W {
        assert!(len <= W::SIZE && i < self.size() && i + len <= self.size());
        if len == 0 {
            return W::MIN;
        }

        let (q0, r0) = divrem::<usize>(i, T::SIZE);
        let (q1, r1) = divrem::<usize>(i + len - 1, T::SIZE);
        if q0 == q1 {
            self[q0].bits(r0, r1 - r0 + 1)
        } else {
            let mut cur = T::SIZE - r0;
            let mut out = self[q0].bits::<W>(r0, cur);
            for n in &self[(q0 + 1)..q1] {
                out |= n.bits::<W>(0, T::SIZE).shiftl(cur);
                cur += T::SIZE;
            }
            out |= self[q1].bits::<W>(0, r1 + 1).shiftl(cur);
            cur += r1 + 1;
            assert_eq!(cur, len);
            out
        }
    }

    /// Test bit at a given position. The value `i` must be less than the bit length.
    ///
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::ops::BitGet;
    /// let vec = vec![0b_00000101u64, 0b01100011, 0b01100000];
    /// assert!( vec.bit(0));
    /// assert!(!vec.bit(1));
    /// assert!( vec.bit(2));
    /// assert!(!vec.bit(16));
    /// let slice = &vec[1..];
    /// assert!( slice.bit(0));
    /// assert!( slice.bit(1));
    /// assert!(!slice.bit(2));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `i >= self.size()`.
    fn bit(&self, i: u64) -> bool {
        assert!(i < self.size(), OUT_OF_BOUNDS);
        let (i, o) = divrem::<usize>(i, T::SIZE);
        self[i].bit(o)
    }

    /// Return the all enabled bit in the container.
    ///
    /// ```
    /// use compacts::bit::ops::BitGet;
    /// let vec = vec![0b_10101010_u8, 0b_11110000_u8];
    /// assert_eq!(vec.ones().collect::<Vec<_>>(), vec![1, 3, 5, 7, 12, 13, 14, 15]);
    /// ```
    fn ones<'a>(&'a self) -> Box<dyn Iterator<Item = u64> + 'a> {
        Box::new(
            self.iter()
                .enumerate()
                .filter(|(_, t)| t.count1() > 0)
                .flat_map(|(i, t)| {
                    let offset = cast::<usize, u64>(i) * T::SIZE;
                    t.ones().map(move |j| j + offset)
                }),
        )
    }
}

impl<T: Bits> BitRank for [T] {
    /// Returns the number of enabled bit in `[0, i)`.
    ///
    /// ```
    /// use compacts::bit::ops::{BitCount, BitRank};
    /// let vec = vec![0b_00000000u8, 0b_01100000, 0b_00010000];
    /// assert_eq!(vec.rank1(10), 0);
    /// assert_eq!(vec.rank1(14), 1);
    /// assert_eq!(vec.rank1(15), 2);
    /// assert_eq!(vec.rank1(16), 2);
    /// assert_eq!(vec.rank1(vec.size()), 3);
    ///
    /// let slice = &vec[1..]; // [0b_01100000, 0b_00010000]
    /// assert_eq!(slice.rank1(8),  2);
    /// assert_eq!(slice.rank1(15), 3);
    /// ```
    ///
    /// ```
    /// # use compacts::bit::ops::BitRank;
    /// # let vec = vec![0b_00000000u8, 0b_01100000, 0b_00010000];
    /// assert_eq!(vec.rank1(  ..  ), 3);
    /// assert_eq!(vec.rank1(10..10), 0);
    /// assert_eq!(vec.rank1(10..14), 1);
    /// assert_eq!(vec.rank1(  ..24), 3);
    /// ```
    fn rank1<Ix: IntoBounds>(&self, r: Ix) -> u64 {
        match r.into_bounds(self.size()) {
            Bounds(i, j) if i == j => 0,
            Bounds(0, i) if i == self.size() => self.count1(),
            Bounds(0, i) => {
                let (q, r) = divrem(i, T::SIZE);
                self[..q].count1() + self[q].rank1(r)
            }
            Bounds(i, j) => {
                let (q0, r0) = divrem::<usize>(i, T::SIZE);
                let (q1, r1) = divrem::<usize>(j - 1, T::SIZE);
                if q0 == q1 {
                    self[q0].rank1(r0..=r1)
                } else {
                    self[q0].rank1(r0..T::SIZE) + self[q0 + 1..q1].count1() + self[q1].rank1(r1 + 1)
                }
            }
        }
    }
}

impl<T: Bits> BitSelect1 for [T] {
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::ops::BitSelect1;
    /// let vec = vec![0b_00000000u8, 0b_01100000, 0b_00010000];
    /// assert_eq!(vec.select1(0), Some(13));
    /// assert_eq!(vec.select1(1), Some(14));
    /// assert_eq!(vec.select1(2), Some(20));
    /// assert_eq!(vec.select1(3), None);
    /// ```
    fn select1(&self, mut n: u64) -> Option<u64> {
        for (i, v) in self.iter().enumerate() {
            let count = v.count1();
            if n < count {
                let select1 = v.select1(n).expect("remain < count");
                return Some(cast::<usize, u64>(i) * T::SIZE + select1);
            }
            n -= count;
        }
        None
    }
}

impl<T: Bits> BitSelect0 for [T] {
    fn select0(&self, mut n: u64) -> Option<u64> {
        for (i, v) in self.iter().enumerate() {
            let count = v.count0();
            if n < count {
                let select0 = v.select0(n).expect("remain < count");
                return Some(cast::<usize, u64>(i) * T::SIZE + select0);
            }
            n -= count;
        }
        None
    }
}

impl<T: Bits> BitPut for [T] {
    /// Enable bit at a given position.
    ///
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::ops::BitPut;
    /// let mut vec = vec![0b_0101u64];
    /// assert_eq!(vec.put1(0), 0);
    /// assert_eq!(vec.put1(1), 1);
    /// assert_eq!(vec.put1(2), 0);
    /// assert_eq!(vec.put1(3), 1);
    /// assert_eq!(vec, vec![0b1111]);
    /// ```
    fn put1(&mut self, i: u64) -> u64 {
        assert!(i < self.size(), OUT_OF_BOUNDS);
        let (i, o) = divrem::<usize>(i, T::SIZE);
        self[i].put1(o)
    }

    /// Disable bit at a given position.
    ///
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::ops::BitPut;
    /// let mut vec = vec![0b_0101u64];
    /// assert_eq!(vec.put0(0), 1);
    /// assert_eq!(vec.put0(1), 0);
    /// assert_eq!(vec.put0(2), 1);
    /// assert_eq!(vec.put0(3), 0);
    /// assert_eq!(vec, vec![0b0000]);
    /// ```
    fn put0(&mut self, i: u64) -> u64 {
        assert!(i < self.size(), OUT_OF_BOUNDS);
        let (i, o) = divrem::<usize>(i, T::SIZE);
        self[i].put0(o)
    }

    /// ```
    /// use compacts::bit::ops::{BitPut, BitGet};
    /// let mut vec = vec![0b_00000000_u8; 8];
    /// vec.puts::<u8>(3, 2, 0b10);
    /// assert_eq!(vec.bits::<u8>(3, 2), 0b10);
    /// vec.puts::<u8>(2, 3, 0b011);
    /// assert_eq!(vec.bits::<u8>(2, 3), 0b011);
    /// vec.puts::<u8>(8, 3, 0b101);
    /// assert_eq!(vec.bits::<u8>(8, 3), 0b101);
    /// ```
    fn puts<W: Word>(&mut self, i: u64, len: u64, num: W) {
        assert!(len <= W::SIZE && i < self.size() && i + len <= self.size());
        if len == 0 {
            return;
        }

        let q0 = cast::<u64, usize>(i / T::SIZE);
        let q1 = cast::<u64, usize>((i + len - 1) / T::SIZE);
        if q0 == q1 {
            // fit in one `T`
            self[q0].puts::<W>(i % T::SIZE, len, num)
        } else {
            // spans many `T`s
            assert!(q0 < q1);
            let offset = i % T::SIZE;
            let mut cur = T::SIZE - offset;
            self[q0].puts::<W>(offset, cur, num.bits(0, cur));
            // if T is a `BoxedSlice<A>`, this loop never happens because `q0 + 1 == q1`.
            for b in &mut self[q0 + 1..q1] {
                b.puts::<W>(0, T::SIZE, num.bits(cur, T::SIZE));
                cur += T::SIZE;
            }
            self[q1].puts::<W>(0, len - cur, num.bits(cur, len - cur));
        }
    }
}

impl<'a, T> IntoSteps for &'a Vec<T>
where
    &'a [T]: IntoSteps,
{
    type Index = <&'a [T] as IntoSteps>::Index;
    type Value = <&'a [T] as IntoSteps>::Value;
    type Steps = <&'a [T] as IntoSteps>::Steps;
    fn into_steps(self) -> Self::Steps {
        self.as_slice().into_steps()
    }
}

pub struct Chunks<'a, T> {
    iter: Enumerate<std::slice::Chunks<'a, T>>,
}

impl<'a, T: Word> IntoSteps for &'a [T] {
    type Index = usize;
    type Value = Cow<'a, [T]>;
    type Steps = Chunks<'a, T>;
    fn into_steps(self) -> Self::Steps {
        let size = BLOCK_SIZE / T::SIZE;
        Chunks {
            iter: self.chunks(cast::<u64, usize>(size)).enumerate(),
        }
    }
}

impl<'a, T: Word> Iterator for Chunks<'a, T> {
    type Item = Step<usize, Cow<'a, [T]>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(index, chunk)| {
            let size = cast(BLOCK_SIZE / T::SIZE);
            if chunk.len() != size {
                let mut vec = chunk.to_vec();
                vec.resize(size, T::MIN);
                let count = chunk.count1();
                let value = Cow::Owned(vec);
                Step {
                    count,
                    index,
                    value,
                }
            } else {
                let count = chunk.count1();
                let value = Cow::Borrowed(chunk);
                Step {
                    count,
                    index,
                    value,
                }
            }
        })
    }
}

pub struct Blocks<'a> {
    iter: Enumerate<std::slice::Iter<'a, Block>>,
}

impl<'a> IntoSteps for &'a [Block] {
    type Index = usize;
    type Value = Slice<'a>;
    type Steps = Blocks<'a>;
    fn into_steps(self) -> Self::Steps {
        Blocks {
            iter: self.iter().enumerate(),
        }
    }
}

impl<'a> Iterator for Blocks<'a> {
    type Item = Step<usize, Slice<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.find(|&(_, b)| b.count1() > 0).map(|(index, b)| {
            let count = b.count1();
            let value = b.as_slice();
            Step {
                count,
                index,
                value,
            }
        })
    }
}

// pub struct Maps<'a> {
//     iter: Box<dyn Iterator<Item = Step<u64, Slice<'a>>> + 'a>,
// }

// impl<'a> IntoSteps for &'a [Map<u32>] {
//     type Index = u64;
//     type Value = Slice<'a>;
//     type Steps = Maps<'a>;
//     fn into_steps(self) -> Self::Steps {
//         Maps {
//             iter: Box::new(self.iter().enumerate().flat_map(|(map_index, map)| {
//                 let offset = Map::<u32>::SIZE / BLOCK_SIZE;
//                 map.into_steps().map(move |step| Step {
//                     index: cast::<u16, u64>(step.index) + cast::<usize, u64>(map_index) * offset,
//                     value: step.value,
//                     count: step.count,
//                 })
//             })),
//         }
//     }
// }

// impl<'a> Iterator for Maps<'a> {
//     type Item = Step<u64, Slice<'a>>;
//     fn next(&mut self) -> Option<Self::Item> {
//         self.iter.next()
//     }
// }

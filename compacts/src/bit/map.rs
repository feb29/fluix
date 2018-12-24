use std::{
    iter::{FromIterator, Zip},
    slice::Iter as SliceIter,
};

use crate::{
    bit::{self, mask, ops::*, Bit, Block, IntoSteps, Mask, Slice, Step},
    num::{cast, divrem, TryCast, Word},
};

/// `Map<T>` can be seen as the bit container that filtered out the empty `Block` from `Vec`.
/// The type parameters `T` specifies the bit size of `Map<T>`.
///
/// ```
/// use compacts::bit::{Map, ops::BitCount};
/// let map = Map::<u32>::default();
/// assert_eq!(map.size(), 1<<32);
/// let map = Map::<u64>::default();
/// assert_eq!(map.size(), 1<<63);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Map<T: Bit = usize> {
    ones: u64,
    keys: Vec<T::Key>,
    data: Vec<Block>,
}
impl<T: Bit> Default for Map<T> {
    fn default() -> Self {
        Self::new_unchecked(0, Vec::new(), Vec::new())
    }
}

impl<T: Bit> Map<T> {
    pub fn new() -> Self {
        Default::default()
    }

    pub(super) fn new_unchecked(ones: u64, keys: Vec<T::Key>, data: Vec<Block>) -> Self {
        Map { ones, keys, data }
    }

    pub fn of<'a>(data: impl IntoIterator<Item = &'a u64>) -> Self {
        let mut map = Self::new();
        for &i in data {
            map.put1(i);
        }
        map
    }

    pub fn keys(&self) -> Keys<'_, T::Key> {
        Keys {
            iter: self.keys.iter(),
        }
    }

    pub fn values(&self) -> Values<'_> {
        Values {
            iter: self.data.iter(),
        }
    }

    pub fn steps(&self) -> Steps<'_, T::Key> {
        Steps {
            zipped: self.keys().zip(self.values()),
        }
    }

    pub fn and<Rhs>(&self, rhs: Rhs) -> Mask<&Self, Rhs, mask::And> {
        bit::and(self, rhs)
    }
    pub fn or<Rhs>(&self, rhs: Rhs) -> Mask<&Self, Rhs, mask::Or> {
        bit::or(self, rhs)
    }
    pub fn and_not<Rhs>(&self, rhs: Rhs) -> Mask<&Self, Rhs, mask::AndNot> {
        bit::and_not(self, rhs)
    }
    pub fn xor<Rhs>(&self, rhs: Rhs) -> Mask<&Self, Rhs, mask::Xor> {
        bit::xor(self, rhs)
    }
}

enum Entry<'a, T: Bit> {
    Occupy {
        idx: usize,
        map: &'a mut Map<T>,
    },
    Vacant {
        idx: usize,
        key: T::Key,
        map: &'a mut Map<T>,
    },
}

impl<T: Bit> Map<T> {
    pub fn block<'a>(&'a self, key: &T::Key) -> Option<&'a Block> {
        self.keys.binary_search(key).map(|i| &self.data[i]).ok()
    }

    pub fn slice<'a>(&'a self, key: &T::Key) -> Slice<'a> {
        Slice::from(self.block(key))
    }

    pub fn blocks(&self) -> impl Iterator<Item = Step<T::Key, &'_ Block>> {
        let keys = self.keys.iter();
        let vals = self.data.iter();
        keys.zip(vals).map(|(&index, value)| {
            let count = value.count1();
            Step {
                index,
                value,
                count,
            }
        })
    }

    pub fn into_blocks(self) -> impl Iterator<Item = Step<T::Key, Block>> {
        let keys = self.keys.into_iter();
        let vals = self.data.into_iter();
        keys.zip(vals).map(|(index, value)| {
            let count = value.count1();
            Step {
                index,
                value,
                count,
            }
        })
    }

    pub fn slices(&self) -> impl Iterator<Item = Step<T::Key, Slice<'_>>> {
        let keys = self.keys.iter();
        let vals = self.data.iter();
        keys.zip(vals).map(|(&index, block)| {
            let count = block.count1();
            let value = block.as_slice();
            Step {
                index,
                value,
                count,
            }
        })
    }

    fn entry<'a>(&'a mut self, key: &T::Key) -> Entry<'a, T> {
        match self.keys.binary_search(key) {
            Ok(idx) => Entry::Occupy { idx, map: self },
            Err(idx) => Entry::Vacant {
                idx,
                key: *key,
                map: self,
            },
        }
    }

    pub fn into_vec(self) -> Vec<Block> {
        assert_eq!(self.keys.len(), self.data.len());
        let mut blocks = if let Some(&last_key) = self.keys.last() {
            let last_index = cast::<T::Key, usize>(last_key);
            Vec::with_capacity(last_index)
        } else {
            Vec::new()
        };

        for Step { index, value, .. } in self.into_blocks() {
            let i = cast::<T::Key, usize>(index);
            if blocks.len() < i + 1 {
                blocks.resize(i + 1, Block::empty());
            }
            blocks.insert(i, value);
        }
        blocks
    }

    /// Shrink an internal vector.
    pub fn shrink_to_fit(&mut self) {
        self.keys.shrink_to_fit();
        self.data.shrink_to_fit();
    }
}

impl<'a, T: Bit> Entry<'a, T> {
    fn or_empty(self) -> &'a mut Block {
        match self {
            Entry::Occupy { idx, map } => &mut map.data[idx],
            Entry::Vacant { idx, key, map } => {
                map.keys.insert(idx, key);
                map.data.insert(idx, Block::empty());
                &mut map.data[idx]
            }
        }
    }

    fn puts<W: Word>(self, i: u64, len: u64, num: W) {
        self.or_empty().puts(i, len, num)
    }

    fn put1(self, i: u64) -> u64 {
        self.or_empty().put1(i)
    }

    fn put0(self, i: u64) -> u64 {
        match self {
            Entry::Occupy { idx, map } => map.data[idx].put0(i),
            Entry::Vacant { .. } => 0,
        }
    }
}

impl<T: Bit> crate::private::Sealed for Map<T> {}

// impl Bits for Map<u32> {
//     /// Potential bit size.
//     const SIZE: u64 = <u32 as Bit>::MAX_SIZE;
//     fn empty() -> Self {
//         Self::default()
//     }
// }

impl<T: Bit> BitCount for Map<T> {
    /// Potential bit size.
    fn size(&self) -> u64 {
        T::MAX_SIZE
    }
    fn count1(&self) -> u64 {
        self.ones
    }
}

impl<T: Bit> BitGet for Map<T> {
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::{Map, ops::BitGet};
    /// let map = Map::<u32>::of(&[65534, 65535, 65536, 65537, 131071]);
    /// assert_eq!(map.bits::<u64>(     0, 64), 0b_0000_0000);
    /// assert_eq!(map.bits::<u64>(    64, 64), 0b_0000_0000);
    /// assert_eq!(map.bits::<u64>( 65530, 60), 0b_1111_0000);
    /// assert_eq!(map.bits::<u64>( 65534, 16), 0b_0000_1111);
    /// assert_eq!(map.bits::<u64>( 65535, 63), 0b_0000_0111);
    /// assert_eq!(map.bits::<u64>( 65536, 63), 0b_0000_0011);
    /// assert_eq!(map.bits::<u64>(131071, 10), 0b_0000_0001);
    /// ```
    fn bits<W: Word>(&self, i: u64, len: u64) -> W {
        assert!(len <= W::SIZE && i < self.size() && i + len <= self.size());
        if len == 0 {
            return W::MIN;
        }

        let (q0, r0) = divrem(i, Block::SIZE);
        let (q1, r1) = divrem(i + len - 1, Block::SIZE);

        if q0 == q1 {
            let len = r1 - r0 + 1;
            self.block(&q0).map_or(W::MIN, |v| v.bits(r0, len))
        } else {
            assert_eq!(q0 + T::Key::ONE, q1);
            let len = Block::SIZE - r0;
            let head = self.block(&q0).map_or(W::MIN, |v| v.bits(r0, len));
            let last = self.block(&q1).map_or(W::MIN, |v| v.bits(0, r1 + 1));
            head | last.shiftl(len)
        }
    }

    /// Test bit at a given position.
    ///
    /// # Examples
    ///
    /// ```
    /// use compacts::{bit::{Block, Map}, bit::ops::BitGet};
    /// let map = Map::<u32>::of(&[0, 80]);
    /// assert!( map.bit(0));
    /// assert!(!map.bit(1));
    /// assert!( map.bit(80));
    /// assert!(!map.bit(81));
    /// assert!(!map.bit(96));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if index out of bounds.
    fn bit(&self, i: u64) -> bool {
        assert!(i < self.size(), bit::OUT_OF_BOUNDS);
        let (i, o) = divrem(i, Block::SIZE);
        self.block(&i).map_or(false, |v| v.bit(o))
    }

    /// # Examples
    ///
    /// ```
    /// use compacts::bit::{Map, ops::BitGet};
    /// let map = Map::<u32>::of(&[0, 80]);
    /// assert_eq!(map.ones().collect::<Vec<_>>(), vec![0, 80]);
    /// ```
    fn ones<'a>(&'a self) -> Box<dyn Iterator<Item = u64> + 'a> {
        Box::new(self.keys.iter().enumerate().flat_map(move |(i, &k)| {
            let offset = cast::<T::Key, u64>(k) * Block::SIZE;
            self.data[i].ones().map(move |b| b + offset)
        }))
    }
}

impl<T: Bit> BitPut for Map<T> {
    fn put1(&mut self, i: u64) -> u64 {
        assert!(i < self.size(), bit::OUT_OF_BOUNDS);
        let (index, offput) = divrem(i, Block::SIZE);
        let diff = self.entry(&index).put1(offput);
        self.ones += diff;
        diff
    }

    fn put0(&mut self, i: u64) -> u64 {
        assert!(i < self.size(), bit::OUT_OF_BOUNDS);
        let (index, offput) = divrem(i, Block::SIZE);
        let diff = self.entry(&index).put0(offput);
        self.ones -= diff;
        diff
    }

    /// # Examples
    ///
    /// ```
    /// use compacts::bit::{Map, ops::{BitCount, BitPut}};
    /// let mut map = Map::<u32>::default();
    /// map.puts::<u8>(3, 2,   0b10); // 4
    /// map.puts::<u8>(8, 3,  0b101); // 4, 8, 10
    /// map.puts::<u8>(2, 3,  0b011); // 2, 3, 8, 10
    /// map.puts::<u8>(7, 4, 0b1111); // 2, 3, 7, 8, 9, 10
    /// map.puts::<u8>(9, 4, 0b0000); // 2, 3, 7, 8
    /// assert_eq!(map.count1(), 4);
    /// ```
    fn puts<W: Word>(&mut self, i: u64, len: u64, bits: W) {
        assert!(len <= W::SIZE && i < self.size() && i + len <= self.size());
        if len == 0 {
            return;
        }

        let prev = self.bits::<W>(i, len);

        let q0 = cast::<u64, T::Key>(i / Block::SIZE);
        let q1 = cast::<u64, T::Key>((i + len - 1) / Block::SIZE);
        if q0 == q1 {
            self.entry(&q0).puts(i % Block::SIZE, len, bits);
        } else {
            assert_eq!(q0 + T::Key::ONE, q1);
            let offset = i % Block::SIZE;

            let cur = Block::SIZE - offset;
            let w = bits.bits(0, cur);
            self.entry(&q0).puts::<W>(offset, cur, w);

            let n = len - cur;
            let w = bits.bits(cur, n);
            self.entry(&q1).puts::<W>(0, n, w);
        }

        let new = bits.count1();
        let old = prev.count1();
        if new >= old {
            self.ones += new - old;
        } else {
            self.ones -= old - new;
        }
    }
}

impl<T: Bit> BitRank for Map<T> {
    /// Test bit at a given position.
    ///
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::{Map, ops::BitRank};
    /// let map = Map::<u32>::of(&[10, 20, 80]);
    /// assert_eq!(map.rank1(   ..   ), 3);
    /// assert_eq!(map.rank1(   .. 80), 2);
    /// assert_eq!(map.rank1(10 .. 80), 2);
    /// assert_eq!(map.rank1(20 .. 80), 1);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if index out of bounds.
    fn rank1<Ix: IntoBounds>(&self, index: Ix) -> u64 {
        let Bounds(i, j) = index.into_bounds(self.size());
        let (hq, hr) = divrem(i, Block::SIZE);
        let (lq, lr) = divrem(j - 1, Block::SIZE);
        match self.keys.binary_search(&hq) {
            Ok(n) | Err(n) if n < self.keys.len() => {
                if hq == lq {
                    self.data[n].rank1(hr..=lr)
                } else {
                    let mut rank = 0;
                    for (j, &k) in self.keys[n..].iter().enumerate() {
                        if k == hq {
                            rank += self.data[j + n].rank1(hr..Block::SIZE);
                        } else if k < lq {
                            rank += self.data[j + n].count1();
                        } else if k == lq {
                            rank += self.data[j + n].rank1(lr + 1);
                            break;
                        }
                    }
                    rank
                }
            }
            _ => 0,
        }
    }
}

impl<T: Bit> BitSelect1 for Map<T> {
    fn select1(&self, mut n: u64) -> Option<u64> {
        for (i, v) in self.data.iter().enumerate() {
            let count = v.count1();
            if n < count {
                // remain < count implies that select1 never be None.
                let select1 = v.select1(n).expect("remain < count");
                return Some(cast::<T::Key, u64>(self.keys[i]) * Block::SIZE + select1);
            }
            n -= count;
        }
        None
    }
}

impl<T: Bit> BitSelect0 for Map<T> {
    fn select0(&self, mut c: u64) -> Option<u64> {
        let mut prev: Option<u64> = None; // prev index
        for (i, value) in self.data.iter().enumerate() {
            let index = cast::<T::Key, u64>(self.keys[i]);

            let len = if let Some(p) = prev {
                // (p, index)
                index - (p + 1)
            } else {
                // [0, index)
                index
            };

            // None:    0..index
            // Some(p): p..index
            let count = value.count0() + Block::SIZE * len;
            if c >= count {
                prev = Some(index);
                c -= count;
                continue;
            }

            // c < count
            let select0 = || {
                use std::iter::{once, repeat_with};

                let iter = repeat_with(|| None)
                    .take(cast::<u64, usize>(len))
                    .chain(once(Some(value)));

                // this block is almost same with [T]
                let mut remain = c;
                for (k, v) in iter.enumerate() {
                    let skipped_bit = cast::<usize, u64>(k) * Block::SIZE;
                    let count0 = if let Some(v) = v {
                        v.count0()
                    } else {
                        Block::SIZE
                    };
                    if remain < count0 {
                        return skipped_bit
                            + if let Some(v) = v {
                                // remain < count implies that select0 never be None.
                                v.select0(remain).expect("remain < count")
                            } else {
                                remain
                            };
                    }
                    remain -= count0;
                }

                unreachable!()
            };

            let skipped = prev.map_or(0, |p| (p + 1) * Block::SIZE);
            return Some(skipped + select0());
        }

        let select = if let Some(&last) = self.keys.last() {
            (cast::<T::Key, u64>(last) + 1) * Block::SIZE + c
        } else {
            c // empty
        };
        if select < self.size() {
            Some(select)
        } else {
            None
        }
    }
}

impl<'a, T: Bit, K, V> FromIterator<Step<K, V>> for Map<T>
where
    K: Word + TryCast<T::Key>,
    V: Into<Block>,
{
    fn from_iter<I>(iterable: I) -> Self
    where
        I: IntoIterator<Item = Step<K, V>>,
    {
        let mut ones = 0;
        let mut keys = Vec::with_capacity(1 << 10);
        let mut data = Vec::with_capacity(1 << 10);

        iterable.into_iter().for_each(|entry| {
            if entry.count == 0 {
                return;
            }

            let index = cast(entry.index);
            let value = entry.value.into();
            let count = entry.count;
            ones += count;
            keys.push(index);
            data.push(value);
        });
        keys.shrink_to_fit();
        data.shrink_to_fit();
        Map::new_unchecked(ones, keys, data)
    }
}

impl<'a, T: Bit> IntoSteps for &'a Map<T> {
    type Index = T::Key;
    type Value = Slice<'a>;
    type Steps = Steps<'a, T::Key>;
    fn into_steps(self) -> Self::Steps {
        assert_eq!(self.keys.len(), self.data.len());
        self.steps()
    }
}

pub struct Keys<'a, K> {
    iter: SliceIter<'a, K>,
}

pub struct Values<'a> {
    iter: SliceIter<'a, Block>,
}

pub struct Steps<'a, K> {
    zipped: Zip<Keys<'a, K>, Values<'a>>,
}

impl<'a, K> Iterator for Keys<'a, K> {
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a> Iterator for Values<'a> {
    type Item = &'a Block;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, K: Word> Iterator for Steps<'a, K> {
    type Item = Step<K, Slice<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.zipped
            .find(|(_, v)| v.count1() > 0)
            .map(|(&index, block)| {
                let count = block.count1();
                let value = block.as_slice();
                Step {
                    count,
                    index,
                    value,
                }
            })
    }
}

use std::{borrow::Cow, iter::FromIterator};

use crate::{
    bits::iter::{And, Not, Or, Xor},
    bits::*,
};

/// `PageMap` is a vector of `Page<K, V>` that are sorted by index `K`.
/// `PageMap` can be seen as a bits container that filtered out the empty `T` from `[T]`.
///
/// The type parameters `K` specifies the bit size of the vector.
/// In other words, the smaller of `K::LENGTH * V::BITS` and `MAX_BITS` is the bit size of `PageMap<K, V>`.
///
/// However, there is no guaranteed that the number of bits reach that size.
/// It can fail to allocate at any point before that size is reached.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PageMap<K: UnsignedInt, V> {
    ones: u64,
    data: Vec<Page<K, V>>,
}

/// `Page` holds value `V` and its index `K`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Page<K: UnsignedInt, V> {
    pub(crate) index: K,
    pub(crate) value: V,
}

impl<K: UnsignedInt, V> Page<K, V> {
    pub fn new(index: K, value: V) -> Self {
        Self { index, value }
    }

    pub fn index(&self) -> &K {
        &self.index
    }
    pub fn value(&self) -> &V {
        &self.value
    }

    fn find(slice: &[Self], index: &K) -> Result<usize, usize> {
        slice.binary_search_by_key(index, |entry| entry.index)
    }

    fn potential_bits() -> u64
    where
        V: FiniteBits,
    {
        // (1<<K::BITS) * V::BITS
        1u64.checked_shl(K::BITS as u32)
            .and_then(|len| len.checked_mul(V::BITS))
            .map_or(MAX_BITS, |bits| std::cmp::min(bits, MAX_BITS))
    }
}

impl<K: UnsignedInt, V> Default for PageMap<K, V> {
    fn default() -> Self {
        let ones = 0;
        let data = Vec::new();
        PageMap { ones, data }
    }
}

impl<K: UnsignedInt, V> AsRef<[Page<K, V>]> for PageMap<K, V> {
    fn as_ref(&self) -> &[Page<K, V>] {
        self.data.as_slice()
    }
}

impl<'a, K: UnsignedInt, V: Clone> IntoIterator for &'a PageMap<K, V> {
    type Item = Page<K, Cow<'a, V>>;
    type IntoIter = Pager<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        Pager::from(self.data.as_slice())
    }
}

impl<'a, K: UnsignedInt, V, U> FromIterator<Page<K, Cow<'a, V>>> for PageMap<K, U>
where
    V: Clone + Count + 'a,
    U: From<V>,
{
    fn from_iter<I>(iterable: I) -> Self
    where
        I: IntoIterator<Item = Page<K, Cow<'a, V>>>,
    {
        let mut ones = 0;
        let mut bits = Vec::with_capacity(1 << 10);

        iterable.into_iter().for_each(|entry| {
            let count = entry.value.as_ref().count1();
            if count == 0 {
                return;
            }
            ones += count;
            let value = entry.value.into_owned().into();
            bits.push(Page::new(entry.index, value));
        });

        bits.shrink_to_fit();
        PageMap::new_unchecked(ones, bits)
    }
}

impl<K: UnsignedInt, V> PageMap<K, V> {
    pub fn new() -> Self {
        Default::default()
    }

    fn new_unchecked(ones: u64, data: Vec<Page<K, V>>) -> Self {
        PageMap { ones, data }
    }

    pub fn and<Rhs>(&self, rhs: Rhs) -> And<&Self, Rhs> {
        And { lhs: self, rhs }
    }

    pub fn or<Rhs>(&self, rhs: Rhs) -> Or<&Self, Rhs> {
        Or { lhs: self, rhs }
    }

    pub fn xor<Rhs>(&self, rhs: Rhs) -> Xor<&Self, Rhs> {
        Xor { lhs: self, rhs }
    }

    pub fn not(&self) -> Not<&Self> {
        Not { val: self }
    }

    // pub fn into_inner(self) -> (u64, Vec<Page<K, V>>) {
    //     (self.ones, self.data)
    // }
}

impl<K: UnsignedInt, V> Count for PageMap<K, V>
where
    V: FiniteBits,
{
    fn bits(&self) -> u64 {
        Page::<K, V>::potential_bits()
    }
    fn count1(&self) -> u64 {
        self.ones
    }
}
impl<K: UnsignedInt, V> Count for [Page<K, V>]
where
    V: FiniteBits,
{
    /// # Examples
    ///
    /// ```
    /// use compacts::bits::{Page, Count};
    /// let slice = [Page::new(9u8, 0u64)];
    /// assert_eq!(slice.bits(), (1 << 8) * 64);
    /// ```
    fn bits(&self) -> u64 {
        Page::<K, V>::potential_bits()
    }

    /// # Examples
    ///
    /// ```
    /// use compacts::bits::{Page, Count};
    /// let slice = [Page::new(9u8, 0b_00001111_11110101u128)];
    /// assert_eq!(slice.bits(), (1 << 8) * 128); // 32768
    /// assert_eq!(slice.count1(), 10);
    /// assert_eq!(slice.count0(), 32758);
    /// ```
    fn count1(&self) -> u64 {
        self.iter().fold(0, |acc, e| acc + e.value.count1())
    }
}

impl<K: UnsignedInt, V> Access for PageMap<K, V>
where
    V: FiniteBits + Access,
{
    fn access(&self, i: u64) -> bool {
        self.data.access(i)
    }
}
impl<K: UnsignedInt, V> Access for [Page<K, V>]
where
    V: FiniteBits + Access,
{
    /// Test bit at a given position.
    ///
    /// # Examples
    ///
    /// ```
    /// use compacts::bits::{Page, Access};
    /// let slice = [Page::new(0usize, 1u16), Page::new(5, 1)];
    /// assert!( slice.access(0));
    /// assert!(!slice.access(1));
    /// assert!( slice.access(80));
    /// assert!(!slice.access(81));
    /// assert!(!slice.access(96));
    /// ```
    ///
    /// We can create a masked bits by slicing entries.
    ///
    /// ```
    /// # use compacts::bits::{Page, Access};
    /// # let slice = [Page::new(0usize, 1u16), Page::new(5, 1)];
    /// let slice = &slice[1..]; // [Page::new(5, 1)]
    /// assert!(!slice.access(0));
    /// assert!(!slice.access(1));
    /// assert!( slice.access(80));
    /// assert!(!slice.access(81));
    /// assert!(!slice.access(96));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if index out of bounds.
    fn access(&self, i: u64) -> bool {
        assert!(i < self.bits(), OUT_OF_BOUNDS);
        let (i, o) = divmod(i, V::BITS);
        self.binary_search_by_key(&i, |e| e.index)
            .map(|k| self[k].value.access(o))
            .unwrap_or_default()
    }
}

impl<K: UnsignedInt, V> Assign<u64> for PageMap<K, V>
where
    V: FiniteBits + Access + Assign<u64>,
{
    type Output = ();
    fn set1(&mut self, i: u64) -> Self::Output {
        assert!(i < self.bits(), OUT_OF_BOUNDS);
        let (index, offset) = divmod(i, V::BITS);
        match Page::find(&*self.data, &index) {
            Ok(j) => {
                if !self.data[j].value.access(offset) {
                    self.ones += 1;
                    self.data[j].value.set1(offset);
                }
            }
            Err(j) => {
                self.ones += 1;
                let mut value = V::empty();
                value.set1(offset);
                let entry = Page::new(index, value);
                self.data.insert(j, entry);
            }
        }
    }

    fn set0(&mut self, i: u64) -> Self::Output {
        assert!(i < self.bits(), OUT_OF_BOUNDS);
        let (index, offset) = divmod(i, V::BITS);
        if let Ok(k) = Page::find(&*self.data, &index) {
            if self.data[k].value.access(offset) {
                self.ones -= 1;
                self.data[k].value.set0(offset);
                if self.data[k].value.count1() == 0 {
                    self.data.remove(k);
                }
            }
        }
    }
}

impl<K: UnsignedInt, V> Rank for PageMap<K, V>
where
    V: FiniteBits + Rank,
{
    fn rank1(&self, i: u64) -> u64 {
        let bits = self.bits();
        assert!(i <= bits, OUT_OF_BOUNDS);
        if i == bits {
            self.ones
        } else {
            self.data.rank1(i)
        }
    }
}
impl<K: UnsignedInt, V> Rank for [Page<K, V>]
where
    V: FiniteBits + Rank,
{
    /// Return the number of enabled bits in `[0, i)`.
    ///
    /// ```
    /// use compacts::bits::{Page, Rank, Count};
    /// let slice = [Page::new(0usize, 0b_00001111_11110000u32), Page::new(3, 0b_01100000_01100000)];
    /// assert_eq!(slice.rank1(10), 6);
    /// assert_eq!(slice.rank1(32), 8);
    /// assert_eq!(slice.rank1(103), 10);
    /// assert_eq!(slice.rank1(slice.bits()), slice.count1());
    /// ```
    ///
    /// Unlike `[T]`, slicing for `[Page<K, V>]` mask the bits.
    ///
    /// ```
    /// # use compacts::bits::{Page, Rank, Count};
    /// # let slice = [Page::new(0usize, 0b_00001111_11110000u32), Page::new(3, 0b_01100000_01100000)];
    /// let slice = &slice[1..]; // [Page::new(3, 0b_01100000_01100000)]
    /// assert_eq!(slice.rank1(10), 0);
    /// assert_eq!(slice.rank1(32), 0);
    /// assert_eq!(slice.rank1(103), 2);
    /// assert_eq!(slice.rank1(slice.bits()), slice.count1());
    /// ```
    fn rank1(&self, i: u64) -> u64 {
        assert!(i <= self.bits(), OUT_OF_BOUNDS);
        let (i, o) = divmod(i, V::BITS);
        let mut rank = 0;
        for entry in self {
            if entry.index < i {
                rank += entry.value.count1();
            } else if entry.index == i {
                rank += entry.value.rank1(o);
                break;
            } else if entry.index > i {
                break;
            }
        }
        rank
    }
}

impl<K: UnsignedInt, V> Select1 for PageMap<K, V>
where
    V: FiniteBits + Select1,
{
    fn select1(&self, n: u64) -> Option<u64> {
        if n < self.count1() {
            self.data.select1(n)
        } else {
            None
        }
    }
}
impl<K: UnsignedInt, V> Select1 for [Page<K, V>]
where
    V: FiniteBits + Select1,
{
    fn select1(&self, mut n: u64) -> Option<u64> {
        for entry in self {
            let count = entry.value.count1();
            if n < count {
                // remain < count implies that select1 never be None.
                let select1 = entry.value.select1(n).expect("remain < count");
                return Some(ucast::<K, u64>(entry.index) * V::BITS + select1);
            }
            n -= count;
        }
        None
    }
}

impl<K: UnsignedInt, V> Select0 for PageMap<K, V>
where
    V: FiniteBits + Select0,
{
    fn select0(&self, n: u64) -> Option<u64> {
        if n < self.count0() {
            self.data.select0(n)
        } else {
            None
        }
    }
}
impl<K: UnsignedInt, V> Select0 for [Page<K, V>]
where
    V: FiniteBits + Select0,
{
    /// # Examples
    ///
    /// ```
    /// use compacts::bits::{Page, Select0};
    /// // [T]: 00000000 00000000 11111011 00000000 00000000 00000000 11111011 00000000 ...
    /// let slice = [Page::new(2usize, 0b_11111011_u8), Page::new(6, 0b_11111011)];
    /// assert_eq!(slice.select0(10), Some(10));
    /// assert_eq!(slice.select0(15), Some(15));
    /// assert_eq!(slice.select0(16), Some(18));
    /// assert_eq!(slice.select0(30), Some(37));
    /// assert_eq!(slice.select0(41), Some(50));
    /// assert_eq!(slice.select0(42), Some(56));
    /// ```
    fn select0(&self, mut c: u64) -> Option<u64> {
        if self.is_empty() {
            return if c < self.bits() { Some(c) } else { None };
        }

        let mut prev: Option<u64> = None; // prev index
        for entry in self {
            let index = ucast::<K, u64>(entry.index);
            let value = &entry.value;

            let len = if let Some(p) = prev {
                // (p, index)
                index - (p + 1)
            } else {
                // [0, index)
                index
            };

            // None:    0..index
            // Some(p): p..index
            let count = value.count0() + V::BITS * len;
            if c >= count {
                prev = Some(index);
                c -= count;
                continue;
            }

            // c < count
            let select0 = || {
                use std::iter::{once, repeat_with};

                let iter = repeat_with(|| None)
                    .take(ucast::<u64, usize>(len))
                    .chain(once(Some(value)));

                // this block is almost same with [T]
                let mut remain = c;
                for (k, v) in iter.enumerate() {
                    let skipped_bits = ucast::<usize, u64>(k) * V::BITS;
                    let count0 = if let Some(v) = v { v.count0() } else { V::BITS };
                    if remain < count0 {
                        return skipped_bits
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

            let skipped_bits = prev.map_or(0, |p| (p + 1) * V::BITS);
            return Some(skipped_bits + select0());
        }

        let select = (ucast::<K, u64>(self[self.len() - 1].index) + 1) * V::BITS + c;
        if select < self.bits() {
            Some(select)
        } else {
            None
        }
    }
}

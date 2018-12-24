use std::{borrow::Cow, iter};

use crate::bits::*;

impl<K, V> Count for Map<Page<K, V>>
where
    K: UnsignedInt,
    V: FiniteBits,
{
    fn bits(&self) -> u64 {
        Page::<K, V>::potential_bits()
    }
    fn count1(&self) -> u64 {
        debug_assert!(self.ones <= self.bits());
        self.ones
    }
}

impl<K, V> Access for Map<Page<K, V>>
where
    K: UnsignedInt,
    V: FiniteBits + Access,
{
    fn access(&self, i: u64) -> bool {
        self.data.access(i)
    }
}

// impl<B: ConstSize + Select1> Select1 for Map<B> {
//     fn select1(&self, c: u64) -> Option<u64> {
//         self.bits.select1(c)
//     }
// }
// impl<B: ConstSize + Rank> Select0 for Map<B> {
//     fn select0(&self, n: u64) -> Option<u64> {
//         self.search0(n)
//     }
// }

// impl<B: UnsignedInt> Insert for Map<B> {
//     fn insert(&mut self, i: u64) -> bool {
//         assert!(i < Self::SIZE, bits::OUT_OF_BOUNDS);
//         match self.address(i) {
//             (k, offset) if k >= self.bits.len() => {
//                 self.bits.resize(k + 1, B::ZERO);
//                 self.bits[k].insert(offset);
//                 self.ones += 1;
//                 false
//             }
//             (k, offset) => {
//                 if !self.bits[k].insert(offset) {
//                     self.ones += 1;
//                     false
//                 } else {
//                     true
//                 }
//             }
//         }
//     }
// }

// impl<B: UnsignedInt> Insert for Map<Words<Box<[B]>>> {
//     fn insert(&mut self, i: u64) -> bool {
//         assert!(i < Self::SIZE, bits::OUT_OF_BOUNDS);
//         match self.address(i) {
//             (k, offset) if k >= self.bits.len() => {
//                 self.bits.resize(k + 1, Words::default());
//                 self.bits[k].insert(offset);
//                 self.ones += 1;
//                 false
//             }
//             (k, offset) => {
//                 if !self.bits[k].insert(offset) {
//                     self.ones += 1;
//                     false
//                 } else {
//                     true
//                 }
//             }
//         }
//     }
// }

// impl<'a, B: UnsignedInt> Insert for Map<Words<Cow<'a, [B]>>> {
//     fn insert(&mut self, i: u64) -> bool {
//         assert!(i < Self::SIZE, bits::OUT_OF_BOUNDS);
//         match self.address(i) {
//             (k, offset) if k >= self.bits.len() => {
//                 self.bits.resize(k + 1, Words::default());
//                 self.bits[k].insert(offset);
//                 self.ones += 1;
//                 false
//             }
//             (k, offset) => {
//                 if !self.bits[k].insert(offset) {
//                     self.ones += 1;
//                     false
//                 } else {
//                     true
//                 }
//             }
//         }
//     }
// }

// impl<B: ConstSize + Remove> Remove for Map<B> {
//     fn remove(&mut self, i: u64) -> bool {
//         assert!(i < Self::SIZE, bits::OUT_OF_BOUNDS);
//         match self.address(i) {
//             (k, _) if k >= self.bits.len() => false,
//             (k, offset) => {
//                 if self.bits[k].remove(offset) {
//                     self.ones -= 1;
//                     true
//                 } else {
//                     false
//                 }
//             }
//         }
//     }
// }

// macro_rules! impl_for_entry {
//     ( $([ $($constraints:tt)*] for $Type:ty ;)+ ) => {
//         $(
//             impl<$($constraints)*> Access for $Type {
//                 fn access(&self, i: u64) -> bool {
//                     assert!(i < Self::SIZE);
//                     let (k, offset) = self.address(i);
//                     self.entry(k).map_or(false, |e| e.v.access(offset))
//                 }
//             }

//             impl<$($constraints)*> Rank for $Type {
//                 fn rank1(&self, i: u64) -> u64 {
//                     assert!(i <= Self::SIZE, bits::OUT_OF_BOUNDS);
//                     let (k, offset) = self.address(i);
//                     let mut rank = 0;
//                     for page in &self.bits {
//                         if page.k < k {
//                             rank += page.v.count1();
//                         } else if page.k == k {
//                             rank += page.v.rank1(offset);
//                             break;
//                         } else if page.k > k {
//                             break;
//                         }
//                     }
//                     rank
//                 }
//             }

//             impl<$($constraints)*> Select1 for $Type {
//                 fn select1(&self, mut n: u64) -> Option<u64> {
//                     for entry in &self.bits {
//                         let count = entry.v.count1();
//                         if n < count {
//                             let k = bits::ucast::<usize, u64>(entry.k);
//                             return Some(k * Words::<T>::SIZE + entry.v.select1(n).unwrap());
//                         }
//                         n -= count;
//                     }
//                     None
//                 }
//             }

//             impl<$($constraints)*> Select0 for $Type {
//                 fn select0(&self, n: u64) -> Option<u64> {
//                     self.search0(n)
//                 }
//             }

//             impl<$($constraints)*> Insert for $Type {
//                 fn insert(&mut self, i: u64) -> bool {
//                     assert!(i < Self::SIZE, bits::OUT_OF_BOUNDS);
//                     let (k, offset) = self.address(i);
//                     match self.search_entry(k) {
//                         Ok(p) => {
//                             if self.bits[p].v.insert(offset) {
//                                 true // already enabled
//                             } else {
//                                 self.ones += 1;
//                                 false
//                             }
//                         }
//                         Err(p) => {
//                             let mut entry = PageDeprecated::new(k, bits::BoxWords::splat(T::ZERO));
//                             entry.v.insert(offset);
//                             self.bits.insert(p, entry);
//                             self.ones += 1;
//                             false
//                         }
//                     }
//                 }
//             }

//             impl<$($constraints)*> Remove for $Type {
//                 fn remove(&mut self, i: u64) -> bool {
//                     assert!(i < Self::SIZE, bits::OUT_OF_BOUNDS);
//                     let (k, offset) = self.address(i);
//                     match self.search_entry(k) {
//                         Ok(k) => {
//                             if self.bits[k].v.remove(offset) {
//                                 self.ones -= 1;
//                                 if self.bits[k].v.count1() == 0 {
//                                     self.bits.remove(k);
//                                 }
//                                 true
//                             } else {
//                                 false
//                             }
//                         }
//                         Err(_) => false,
//                     }
//                 }
//             }
//         )+
//     }
// }
// impl_for_entry!(
//     [    T: UnsignedInt] for Map<PageDeprecated<Box<[T]>>>;
//     ['c, T: UnsignedInt] for Map<PageDeprecated<Cow<'c, [T]>>>;
// );

// macro_rules! impl_for_all {
//     ( $([ $($constraints:tt)*] for $Type:ty ;)+ ) => {
//         $(
//             impl<$($constraints)*> $Type {
//                 #[inline]
//                 pub fn get<'a, Ix>(&'a self, index: Ix) -> Ix::Output
//                 where
//                     Ix: bits::Index<&'a Self>,
//                 {
//                     index.get(self)
//                 }

//                 #[inline]
//                 pub fn rank1(&self, i: u64) -> u64 {
//                     <Self as Rank>::rank1(self, i)
//                 }
//                 #[inline]
//                 pub fn rank0(&self, i: u64) -> u64 {
//                     <Self as Rank>::rank0(self, i)
//                 }

//                 #[inline]
//                 pub fn insert(&mut self, i: u64) -> bool {
//                     <Self as Insert>::insert(self, i)
//                 }
//                 #[inline]
//                 pub fn remove(&mut self, i: u64) -> bool {
//                     <Self as Remove>::remove(self, i)
//                 }
//             }

//             impl<$($constraints)*> From<Vec<u64>> for $Type {
//                 fn from(vec: Vec<u64>) -> Self {
//                     let mut bits = <$Type as Default>::default();
//                     for bit in vec.into_iter() {
//                         bits.insert(bit);
//                     }
//                     bits
//                 }
//             }
//             impl<$($constraints)*> From<&[u64]> for $Type {
//                 fn from(vec: &[u64]) -> Self {
//                     let mut bits = <$Type as Default>::default();
//                     for &bit in vec.iter() {
//                         bits.insert(bit);
//                     }
//                     bits
//                 }
//             }
//         )+
//     }
// }
// impl_for_all!(
//     [    T: UnsignedInt] for Map<T>;
//     [    T: UnsignedInt] for Map<Words<Box<[T]>>>;
//     ['c, T: UnsignedInt] for Map<Words<Cow<'c, [T]>>>;
//     [    T: UnsignedInt] for Map<PageDeprecated<Box<[T]>>>;
//     ['c, T: UnsignedInt] for Map<PageDeprecated<Cow<'c, [T]>>>;
// );

// pub struct Chunks<'a, T: UnsignedInt> {
//     iter: std::iter::Enumerate<std::slice::Chunks<'a, T>>,
// }
// impl<'a, T: UnsignedInt> Iterator for Chunks<'a, T> {
//     type Item = PageDeprecated<Cow<'a, [T]>>;
//     fn next(&mut self) -> Option<Self::Item> {
//         self.iter
//             .next()
//             .map(|(i, words)| PageDeprecated::new(i, words))
//     }
// }

// pub struct Pager<'a, B> {
//     iter: std::iter::Enumerate<std::slice::Iter<'a, Words<B>>>,
// }

// impl<'a, T: UnsignedInt> Iterator for Pager<'a, Box<[T]>> {
//     type Item = PageDeprecated<Cow<'a, [T]>>;
//     fn next(&mut self) -> Option<Self::Item> {
//         while let Some((i, words)) = self.iter.next() {
//             if words.is_empty() {
//                 continue;
//             }
//             return Some(PageDeprecated::new(i, words.as_cow()));
//         }
//         None
//     }
// }
// impl<'a: 'cow, 'cow, T: UnsignedInt> Iterator for Pager<'a, Cow<'cow, [T]>> {
//     type Item = PageDeprecated<Cow<'a, [T]>>;
//     fn next(&mut self) -> Option<Self::Item> {
//         while let Some((i, words)) = self.iter.next() {
//             if let Some(cow) = words.as_ref() {
//                 return Some(PageDeprecated::new(i, Words::from(cow.as_ref())));
//             } else {
//                 continue;
//             }
//         }
//         None
//     }
// }

// pub struct Entries<'a, T> {
//     // all entries should be sorted by k.
//     iter: std::slice::Iter<'a, PageDeprecated<T>>,
// }

// impl<'a, T: UnsignedInt> Iterator for Entries<'a, Box<[T]>> {
//     type Item = PageDeprecated<Cow<'a, [T]>>;
//     fn next(&mut self) -> Option<Self::Item> {
//         while let Some(entry) = self.iter.next() {
//             if entry.v.is_empty() {
//                 continue;
//             }
//             return Some(PageDeprecated::new(entry.k, &entry.v));
//         }
//         None
//     }
// }
// impl<'a: 'cow, 'cow, T: UnsignedInt> Iterator for Entries<'a, Cow<'cow, [T]>> {
//     type Item = PageDeprecated<Cow<'cow, [T]>>;
//     fn next(&mut self) -> Option<Self::Item> {
//         while let Some(entry) = self.iter.next() {
//             let k = entry.k;
//             return entry
//                 .v
//                 .as_ref()
//                 .map(|cow| PageDeprecated::new(k, cow.as_ref()));
//         }
//         None
//     }
// }

// impl<'a, T: UnsignedInt> IntoIterator for &'a Map<T> {
//     type Item = PageDeprecated<Cow<'a, [T]>>;
//     type IntoIter = Chunks<'a, T>;
//     fn into_iter(self) -> Self::IntoIter {
//         Chunks {
//             iter: self.bits.chunks(bits::SHORT_BIT_MAX as usize).enumerate(),
//         }
//     }
// }

// impl<'a, T: UnsignedInt> IntoIterator for &'a Map<Words<Box<[T]>>> {
//     type Item = PageDeprecated<Cow<'a, [T]>>;
//     type IntoIter = Pager<'a, Box<[T]>>;
//     fn into_iter(self) -> Self::IntoIter {
//         Pager {
//             iter: self.bits.iter().enumerate(),
//         }
//     }
// }
// impl<'a: 'cow, 'cow, T: UnsignedInt> IntoIterator for &'a Map<Words<Cow<'cow, [T]>>> {
//     type Item = PageDeprecated<Cow<'cow, [T]>>;
//     type IntoIter = Pager<'a, Cow<'cow, [T]>>;
//     fn into_iter(self) -> Self::IntoIter {
//         Pager {
//             iter: self.bits.iter().enumerate(),
//         }
//     }
// }

// impl<'a, T: UnsignedInt> IntoIterator for &'a Map<PageDeprecated<Box<[T]>>> {
//     type Item = PageDeprecated<Cow<'a, [T]>>;
//     type IntoIter = Entries<'a, Box<[T]>>;
//     fn into_iter(self) -> Self::IntoIter {
//         Entries {
//             iter: self.bits.iter(),
//         }
//     }
// }
// impl<'a: 'cow, 'cow, T: UnsignedInt> IntoIterator for &'a Map<PageDeprecated<Cow<'cow, [T]>>> {
//     type Item = PageDeprecated<Cow<'cow, [T]>>;
//     type IntoIter = Entries<'a, Cow<'cow, [T]>>;
//     fn into_iter(self) -> Self::IntoIter {
//         Entries {
//             iter: self.bits.iter(),
//         }
//     }
// }

// impl<'a, T: UnsignedInt> iter::FromIterator<PageDeprecated<Cow<'a, [T]>>> for Map<Words<Box<[T]>>> {
//     fn from_iter<I>(iter: I) -> Self
//     where
//         I: IntoIterator<Item = PageDeprecated<Cow<'a, [T]>>>,
//     {
//         let mut ones = 0;
//         let mut bits = Vec::with_capacity(1 << 10);

//         for p in iter {
//             let k = p.k;
//             let words = p.v; // Words<Cow<[T]>>

//             let count = words.count1();
//             if count == 0 {
//                 continue;
//             }
//             ones += count;
//             bits.resize(k + 1, Words::<Box<[T]>>::empty());
//             bits.insert(k, words.into());
//         }
//         bits.shrink_to_fit();
//         Map::new_unchecked(ones, bits)
//     }
// }

// impl<'a, T: UnsignedInt> iter::FromIterator<PageDeprecated<Cow<'a, [T]>>>
//     for Map<PageDeprecated<Box<[T]>>>
// {
//     fn from_iter<I>(iter: I) -> Self
//     where
//         I: IntoIterator<Item = PageDeprecated<Cow<'a, [T]>>>,
//     {
//         let mut ones = 0;
//         let mut bits = Vec::with_capacity(1 << 10);

//         for p in iter {
//             let k = p.k;
//             let v = p.v;

//             let count = v.count1();
//             if count == 0 {
//                 continue;
//             }
//             ones += count;
//             bits.push(PageDeprecated::new(k, v));
//         }
//         bits.shrink_to_fit();
//         Map::new_unchecked(ones, bits)
//     }
// }

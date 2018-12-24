// use std::{borrow::Cow, iter::FromIterator};

// use crate::{
//     bits::iter::{And, Not, Or, Xor},
//     bits::*,
// };

// impl<K: UnsignedInt, V> PageMap<K, V> {
//     // #[inline]
//     // pub fn get<'a, Ix>(&'a self, index: Ix) -> Ix::Output
//     // where
//     //     Ix: Index<&'a Self>,
//     // {
//     //     index.get(self)
//     // }

//     pub fn and<Rhs>(&self, rhs: Rhs) -> And<&Self, Rhs> {
//         And { lhs: self, rhs }
//     }
//     pub fn or<Rhs>(&self, rhs: Rhs) -> Or<&Self, Rhs> {
//         Or { lhs: self, rhs }
//     }
//     pub fn xor<Rhs>(&self, rhs: Rhs) -> Xor<&Self, Rhs> {
//         Xor { lhs: self, rhs }
//     }
//     pub fn not(&self) -> Not<&Self> {
//         Not { val: self }
//     }
// }

// pub struct Entries<'a, K: UnsignedInt, V> {
//     iter: std::slice::Iter<'a, Page<K, V>>, // V should be sorted by K.
// }

// impl<'a, K: UnsignedInt, V: Clone> Iterator for Entries<'a, K, V> {
//     type Item = Page<K, Cow<'a, V>>;
//     fn next(&mut self) -> Option<Self::Item> {
//         self.iter
//             .next()
//             .map(|e| Page::new(e.index, Cow::Borrowed(&e.value)))
//     }
// }

// impl<'a, K: UnsignedInt, V: Clone> IntoIterator for &'a PageMap<K, V> {
//     type Item = Page<K, Cow<'a, V>>;
//     type IntoIter = Entries<'a, K, V>;
//     fn into_iter(self) -> Self::IntoIter {
//         Entries {
//             iter: self.data.iter(),
//         }
//     }
// }

// impl<K: UnsignedInt, V, A> From<A> for PageMap<K, V>
// where
//     A: AsRef<[u64]>,
//     Self: Assign<u64>,
// {
//     fn from(data: A) -> Self {
//         let mut bv = Self::new();
//         for &i in data.as_ref() {
//             bv.set1(i);
//         }
//         bv
//     }
// }

// impl<'a, K: UnsignedInt, V, U> FromIterator<Page<K, Cow<'a, V>>> for PageMap<K, U>
// where
//     V: Clone + Count + 'a,
//     U: From<V>,
// {
//     fn from_iter<I>(iterable: I) -> Self
//     where
//         I: IntoIterator<Item = Page<K, Cow<'a, V>>>,
//     {
//         let mut ones = 0;
//         let mut bits = Vec::with_capacity(1 << 10);

//         for entry in iterable {
//             let count = entry.value.as_ref().count1();
//             if count == 0 {
//                 continue;
//             }

//             ones += count;
//             let value = entry.value.into_owned().into();
//             bits.push(Page::new(entry.index, value));
//         }
//         bits.shrink_to_fit();
//         PageMap::new_unchecked(ones, bits)
//     }
// }

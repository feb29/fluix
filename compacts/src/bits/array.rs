use std::{borrow::Cow, slice};

use crate::{
    bits,
    bits::*,
    bits::{BoxWords, CowWords, UnsignedInt, Words},
};

impl<T> Default for Words<T> {
    fn default() -> Self {
        Words(None)
    }
}

impl<T> Words<T> {
    pub fn as_ref(&self) -> Option<&T> {
        self.0.as_ref()
    }

    pub fn as_mut(&mut self) -> Option<&mut T> {
        self.0.as_mut()
    }
}

impl<T> ConstSize for Words<T> {
    const SIZE: u64 = bits::SHORT_BIT_MAX;
}

impl<T: UnsignedInt> BoxWords<T> {
    pub const LEN: usize = (Self::SIZE / T::SIZE) as usize;
}

impl<T: UnsignedInt> CowWords<'_, T> {
    pub const LEN: usize = (Self::SIZE / T::SIZE) as usize;
}

impl<T: UnsignedInt> From<CowWords<'_, T>> for BoxWords<T> {
    fn from(Words(v): CowWords<'_, T>) -> Self {
        Words(v.map(|cow| cow.into_owned().into_boxed_slice()))
    }
}
impl<T: UnsignedInt> From<BoxWords<T>> for CowWords<'_, T> {
    fn from(Words(v): BoxWords<T>) -> Self {
        Words(v.map(|arr| Cow::Owned(arr.into_vec())))
    }
}

impl<'a, T: UnsignedInt> From<&'a BoxWords<T>> for CowWords<'a, T> {
    fn from(v: &'a BoxWords<T>) -> Self {
        Words(v.as_ref().map(|ws| Cow::Borrowed(&ws[..])))
    }
}
impl<'a, T: UnsignedInt> From<&'a [T]> for CowWords<'a, T> {
    fn from(slice: &'a [T]) -> Self {
        Words(Some(Cow::Borrowed(&slice[0..Self::LEN])))
    }
}

impl<T: UnsignedInt> From<Vec<T>> for BoxWords<T> {
    fn from(mut vec: Vec<T>) -> Self {
        vec.resize(Self::LEN, T::ZERO);
        Words(Some(vec.into_boxed_slice()))
    }
}
impl<T: UnsignedInt> From<Vec<T>> for CowWords<'_, T> {
    fn from(mut vec: Vec<T>) -> Self {
        vec.resize(Self::LEN, T::ZERO);
        Words(Some(Cow::Owned(vec)))
    }
}

impl<T: UnsignedInt> BoxWords<T> {
    /// Return an empty Words.
    pub fn empty() -> Self {
        Words(None)
    }

    /// Constructs a new instance with each element initialized to value.
    pub fn splat(value: T) -> Self {
        Words(Some(vec![value; Self::LEN].into_boxed_slice()))
    }

    pub fn len(&self) -> usize {
        self.as_cow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.as_cow().is_empty()
    }

    pub fn iter<'r>(&'r self) -> impl Iterator<Item = T> + 'r {
        self.into_iter()
    }
}

impl<T: UnsignedInt> CowWords<'_, T> {
    /// Return an empty Words.
    pub fn empty() -> Self {
        Words(None)
    }

    /// Constructs a new instance with each element initialized to value.
    pub fn splat(value: T) -> Self {
        Words(Some(Cow::Owned(vec![value; Self::LEN])))
    }

    pub fn len(&self) -> usize {
        match self.as_ref() {
            None => 0,
            Some(ref vec) => vec.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter<'r>(&'r self) -> impl Iterator<Item = T> + 'r {
        self.into_iter()
    }
}

impl<T: UnsignedInt> BoxWords<T> {
    pub(crate) fn as_cow(&self) -> CowWords<'_, T> {
        Words::from(self)
    }

    fn init(&mut self) -> &mut [T] {
        if self.0.is_none() {
            *self = Self::splat(T::ZERO);
        }
        self.0.as_mut().unwrap()
    }
}

impl<'r, T: UnsignedInt> IntoIterator for &'r BoxWords<T> {
    type Item = T;
    type IntoIter = WordsIter<'r, T>;
    fn into_iter(self) -> Self::IntoIter {
        WordsIter(self.as_ref().map(|b| b.into_iter().cloned()))
    }
}
impl<'r, 'a, T: UnsignedInt> IntoIterator for &'r CowWords<'a, T> {
    type Item = T;
    type IntoIter = WordsIter<'r, T>;
    fn into_iter(self) -> Self::IntoIter {
        WordsIter(self.as_ref().map(|b| b.into_iter().cloned()))
    }
}

pub struct WordsIter<'a, T: UnsignedInt>(Option<std::iter::Cloned<slice::Iter<'a, T>>>);

impl<'a, T: UnsignedInt> Iterator for WordsIter<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut().and_then(|i| i.next())
    }
}

impl<T: UnsignedInt> Access for BoxWords<T> {
    fn access(&self, i: u64) -> bool {
        assert!(i < Self::SIZE, bits::OUT_OF_BOUNDS);
        self.as_cow().access(i)
    }
}
impl<T: UnsignedInt> Access for CowWords<'_, T> {
    fn access(&self, i: u64) -> bool {
        assert!(i < Self::SIZE, bits::OUT_OF_BOUNDS);
        self.as_ref().map_or(false, |cow| cow.access(i))
    }
}

impl<T: UnsignedInt> Count for BoxWords<T> {
    fn size(&self) -> u64 {
        Self::SIZE
    }
    fn count1(&self) -> u64 {
        self.as_cow().count1()
    }
}
impl<T: UnsignedInt> Count for CowWords<'_, T> {
    fn size(&self) -> u64 {
        Self::SIZE
    }
    fn count1(&self) -> u64 {
        self.as_ref().map_or(0, |cow| cow.count1())
    }
}

impl<T: UnsignedInt> Rank for BoxWords<T> {
    fn rank1(&self, i: u64) -> u64 {
        self.as_cow().rank1(i)
    }
}
impl<T: UnsignedInt> Rank for CowWords<'_, T> {
    fn rank1(&self, i: u64) -> u64 {
        assert!(i <= Self::SIZE, bits::OUT_OF_BOUNDS);
        self.as_ref().map_or(0, |cow| cow.rank1(i))
    }
}

impl<T: UnsignedInt> Select1 for BoxWords<T> {
    fn select1(&self, n: u64) -> Option<u64> {
        self.as_cow().select1(n)
    }
}
impl<T: UnsignedInt> Select0 for BoxWords<T> {
    fn select0(&self, n: u64) -> Option<u64> {
        self.as_cow().select0(n)
    }
}
impl<T: UnsignedInt> Select1 for CowWords<'_, T> {
    fn select1(&self, n: u64) -> Option<u64> {
        if n < self.count1() {
            self.as_ref().expect("should not happen").select1(n)
        } else {
            None
        }
    }
}
impl<T: UnsignedInt> Select0 for CowWords<'_, T> {
    fn select0(&self, n: u64) -> Option<u64> {
        if n < self.count0() {
            self.as_ref().map_or(Some(n), |bv| bv.select0(n))
        } else {
            None
        }
    }
}

impl<T: UnsignedInt> Insert for BoxWords<T> {
    fn insert(&mut self, i: u64) -> bool {
        assert!(i < Self::SIZE);
        self.init().insert(i)
    }
}
impl<T: UnsignedInt> Insert for CowWords<'_, T> {
    fn insert(&mut self, i: u64) -> bool {
        assert!(i < Self::SIZE);
        if self.0.is_none() {
            *self = Self::splat(T::ZERO);
        }
        let bv = self.as_mut().unwrap();
        <[T] as Insert>::insert(bv.to_mut(), i)
    }
}

impl<T: UnsignedInt> Remove for BoxWords<T> {
    fn remove(&mut self, i: u64) -> bool {
        assert!(i < Self::SIZE);
        if let Some(bv) = self.as_mut() {
            bv.remove(i)
        } else {
            false
        }
    }
}
impl<T: UnsignedInt> Remove for CowWords<'_, T> {
    fn remove(&mut self, i: u64) -> bool {
        assert!(i < Self::SIZE);
        if let Some(bv) = self.as_mut() {
            <[T] as Remove>::remove(bv.to_mut(), i)
        } else {
            false
        }
    }
}

impl<'a, T: UnsignedInt> std::ops::BitAnd<CowWords<'a, T>> for CowWords<'a, T> {
    type Output = CowWords<'a, T>;
    fn bitand(self, that: CowWords<'a, T>) -> Self::Output {
        Words(match (self.0, that.0) {
            (None, _) | (_, None) => None,
            (Some(ref buf), _) | (_, Some(ref buf)) if buf.is_empty() => None,
            (Some(mut lhs), Some(rhs)) => {
                assert_eq!(lhs.len(), rhs.len());

                let ones = {
                    let zip = lhs.to_mut().iter_mut().zip(rhs.iter());
                    let mut acc = 0;
                    for (x, y) in zip {
                        *x &= *y;
                        acc += x.count1();
                    }
                    acc
                };

                if ones > 0 {
                    Some(lhs)
                } else {
                    None
                }
            }
        })
    }
}

impl<'a, T: UnsignedInt> std::ops::BitOr<CowWords<'a, T>> for CowWords<'a, T> {
    type Output = CowWords<'a, T>;

    fn bitor(self, that: CowWords<'a, T>) -> Self::Output {
        Words(match (self.0, that.0) {
            (None, None) => None,
            (Some(buf), None) | (None, Some(buf)) => Some(buf),
            (Some(mut lhs), Some(rhs)) => {
                assert_eq!(lhs.len(), rhs.len());
                {
                    let zip = lhs.to_mut().iter_mut().zip(rhs.iter());
                    for (x, y) in zip {
                        *x |= *y;
                    }
                }
                Some(lhs)
            }
        })
    }
}

impl<'a, T: UnsignedInt> std::ops::BitXor<CowWords<'a, T>> for CowWords<'a, T> {
    type Output = CowWords<'a, T>;

    fn bitxor(self, that: CowWords<'a, T>) -> Self::Output {
        Words(match (self.0, that.0) {
            (None, None) => None,
            (Some(buf), None) | (None, Some(buf)) => Some(buf),
            (Some(mut lhs), Some(rhs)) => {
                assert_eq!(lhs.len(), rhs.len());
                {
                    let lhs_vec = lhs.to_mut();
                    let zip = lhs_vec.iter_mut().zip(rhs.iter());
                    for (x, y) in zip {
                        *x ^= *y;
                    }
                };
                Some(lhs)
            }
        })
    }
}

impl<'a, T: UnsignedInt> std::ops::Not for CowWords<'a, T> {
    type Output = CowWords<'a, T>;
    fn not(self) -> Self::Output {
        Words(match self.0 {
            Some(mut buf) => {
                let ones = {
                    let vec = buf.to_mut();
                    vec.resize(BoxWords::<T>::LEN, T::ZERO);
                    let mut acc = 0;
                    for i in 0..vec.len() {
                        vec[i] = !vec[i];
                        acc += vec[i].count1();
                    }
                    acc
                };
                if ones > 0 {
                    Some(buf)
                } else {
                    None
                }
            }
            None => Some(Cow::Owned(vec![!T::ZERO; BoxWords::<T>::LEN])),
        })
    }
}

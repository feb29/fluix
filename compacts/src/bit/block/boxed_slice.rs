use std::{borrow::Cow, fmt, ops::Index};

use crate::{
    bit::ops::*,
    bit::OUT_OF_BOUNDS,
    num::{cast, Word, Words},
};

/// A boxed slice of words.
#[derive(Clone)]
pub struct BoxedSlice<A> {
    pub(crate) ones: u32,
    pub(crate) data: Option<Box<A>>,
}

impl<A> crate::private::Sealed for BoxedSlice<A> {}

impl<A: Words> fmt::Debug for BoxedSlice<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(slice) = self.as_ref() {
            f.debug_list().entries(slice).finish()
        } else {
            f.pad("BoxedSlice")
        }
    }
}

impl<A: Words> PartialEq for BoxedSlice<A> {
    fn eq(&self, that: &BoxedSlice<A>) -> bool {
        if self.ones != that.ones {
            return false;
        }
        self.as_ref() == that.as_ref()
    }
}
impl<A: Words> Eq for BoxedSlice<A> {}

impl<A> Default for BoxedSlice<A> {
    #[inline]
    fn default() -> Self {
        BoxedSlice {
            ones: 0,
            data: None,
        }
    }
}

impl<A: Words> Index<usize> for BoxedSlice<A> {
    type Output = A::Word;
    fn index(&self, i: usize) -> &Self::Output {
        static MSG: &str = "index out of bounds: not allocated";
        &self.as_ref().expect(MSG)[i]
    }
}

impl<A: Words> From<A> for BoxedSlice<A> {
    fn from(array: A) -> Self {
        let ones = cast(array.as_slice().count1());
        let data = Some(Box::new(array));
        BoxedSlice { ones, data }
    }
}
impl<A: Words> From<&'_ A> for BoxedSlice<A> {
    fn from(array: &A) -> Self {
        let ones = cast(array.as_slice().count1());
        let data = Some(Box::new(*array));
        BoxedSlice { ones, data }
    }
}

impl<A: Words> From<Vec<A::Word>> for BoxedSlice<A> {
    fn from(vec: Vec<A::Word>) -> Self {
        assert_eq!(vec.len(), A::LEN);
        let mut block = Self::splat(A::Word::MIN);
        block.copy_from_slice(&vec);
        block
    }
}
impl<A: Words> From<&'_ [A::Word]> for BoxedSlice<A> {
    fn from(slice: &[A::Word]) -> Self {
        assert_eq!(slice.len(), A::LEN);
        let mut block = Self::splat(A::Word::MIN);
        block.copy_from_slice(slice);
        block
    }
}

impl<A: Words> BoxedSlice<A> {
    pub fn splat(value: A::Word) -> Self {
        let array = A::splat(value);
        let ones = cast(array.as_slice().count1());
        let data = Some(Box::new(array));
        BoxedSlice { ones, data }
    }

    pub fn as_ref(&self) -> Option<&[A::Word]> {
        self.data.as_ref().map(|a| a.as_slice())
    }

    // pub fn as_mut(&mut self) -> Option<&mut [A::Word]> {
    //     self.data.as_mut().map(|a| a.as_slice_mut())
    // }

    pub fn as_cow(&self) -> Option<Cow<[A::Word]>> {
        self.data.as_ref().map(|a| Cow::Borrowed(a.as_slice()))
    }

    fn copy_from_slice<T: AsRef<[A::Word]>>(&mut self, data: T) {
        let this = self.alloc().as_slice_mut();
        let that = data.as_ref();
        this[..that.len()].copy_from_slice(that);
        self.ones = cast(this.count1());
    }

    fn alloc(&mut self) -> &mut A {
        if self.data.is_none() {
            *self = Self::splat(A::Word::MIN);
        }
        self.data.as_mut().unwrap()
    }

    // pub(crate) fn chunks<'a>(&'a self, bit_chunk_size: u64) -> Vec<Option<&'a [A::Word]>> {
    //     assert!(Self::SIZE % bit_chunk_size == 0);
    //     if let Some(array) = &self.data {
    //         let chunk_size = bit_chunk_size / <A::Word as Bits>::SIZE;
    //         assert!(chunk_size > 0);
    //         array
    //             .as_slice()
    //             .chunks(cast(chunk_size))
    //             .map(Some)
    //             .collect()
    //     } else {
    //         let len = cast::<u64, usize>(Self::SIZE / bit_chunk_size);
    //         vec![None; len]
    //     }
    // }
}

impl<A: Words> Bits for BoxedSlice<A> {
    const SIZE: u64 = A::SIZE;
    fn empty() -> Self {
        Self::default()
    }
}

impl<A: Words> BitCount for BoxedSlice<A> {
    fn size(&self) -> u64 {
        Self::SIZE
    }
    fn count1(&self) -> u64 {
        u64::from(self.ones)
    }
}

impl<A: Words> BitGet for BoxedSlice<A> {
    fn bits<W: Word>(&self, i: u64, len: u64) -> W {
        assert!(len <= W::SIZE && i < self.size() && i + len <= self.size());
        self.data
            .as_ref()
            .map_or(W::MIN, |a| a.as_slice().bits(i, len))
    }

    fn bit(&self, i: u64) -> bool {
        self.data.as_ref().map_or(false, |a| a.as_slice().bit(i))
    }

    fn ones<'a>(&'a self) -> Box<dyn Iterator<Item = u64> + 'a> {
        if let Some(a) = self.data.as_ref() {
            a.as_slice().ones()
        } else {
            Box::new(std::iter::empty())
        }
    }
}

impl<A: Words> BitPut for BoxedSlice<A> {
    fn put1(&mut self, i: u64) -> u64 {
        assert!(i < self.size(), OUT_OF_BOUNDS);
        let diff = self.alloc().as_slice_mut().put1(i);
        self.ones += cast::<u64, u32>(diff);
        diff
    }
    fn put0(&mut self, i: u64) -> u64 {
        assert!(i < self.size(), OUT_OF_BOUNDS);
        let diff = self.alloc().as_slice_mut().put0(i);
        self.ones -= cast::<u64, u32>(diff);
        diff
    }

    fn puts<W: Word>(&mut self, i: u64, len: u64, bits: W) {
        assert!(len <= W::SIZE && i < self.size() && i + len <= self.size());
        if len == 0 {
            return;
        }
        let prev = self.bits::<W>(i, len);
        self.alloc().as_slice_mut().puts(i, len, bits);

        let new = bits.rank1(len);
        let old = prev.count1();
        if new >= old {
            self.ones += cast::<u64, u32>(new - old);
        } else {
            self.ones -= cast::<u64, u32>(old - new);
        }
    }
}

impl<A: Words> BitRank for BoxedSlice<A> {
    fn rank1<Ix: IntoBounds>(&self, r: Ix) -> u64 {
        // this is an assertion for when data is None
        let b = r.into_bounds(self.size());
        self.data.as_ref().map_or(0, |a| a.rank1(b))
    }
}

impl<A: Words> BitSelect1 for BoxedSlice<A> {
    fn select1(&self, n: u64) -> Option<u64> {
        self.data.as_ref().and_then(|a| a.as_slice().select1(n))
    }
}
impl<A: Words> BitSelect0 for BoxedSlice<A> {
    fn select0(&self, n: u64) -> Option<u64> {
        self.data
            .as_ref()
            .map_or(Some(n), |a| a.as_slice().select0(n))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eq() {
        let a = BoxedSlice::<[u64; 1024]>::empty();
        let b = BoxedSlice::<[u64; 1024]>::empty();
        let c = BoxedSlice::<[u64; 1024]>::splat(0);
        assert_eq!(a, b);
        assert_ne!(a, c);
        let d = BoxedSlice::<[u64; 1024]>::splat(3);
        let e = BoxedSlice::<[u64; 1024]>::splat(3);
        assert_eq!(d, e);
    }

    #[test]
    fn bits() {
        let b = BoxedSlice::<[u8; 8192]>::empty();
        assert_eq!(b.bits::<u64>(100, 63), 0);
        assert_eq!(b.bits::<u64>(163, 17), 0);

        let b = BoxedSlice::<[u8; 8192]>::splat(0b_0001_1100);
        assert_eq!(b.bits::<u8>(0, 3), 0b_0000_0100_u8);
        assert_eq!(b.bits::<u8>(0, 4), 0b_0000_1100_u8);
        assert_eq!(b.bits::<u8>(6, 6), 0b_0011_0000_u8);
    }

    #[test]
    fn puts() {
        let mut b = BoxedSlice::<[u8; 8192]>::empty();
        b.puts::<u64>(0, 3, 0b001);
        b.puts::<u64>(0, 3, 0b010);
        assert_eq!(b.count1(), 1);
        b.puts::<u64>(1, 3, 0b110);
        assert_eq!(b.count1(), 2);
    }
}

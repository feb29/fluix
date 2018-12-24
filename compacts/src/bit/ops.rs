use std::ops;

use crate::{
    bit,
    num::{cast, search_index, Word},
    private,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Index {
    /// `i`
    Exact(u64),
    /// `[i, j)`
    Range(u64, u64),
}

pub trait IntoIndex: private::Sealed {
    fn into_bit(self, bit_size: u64) -> Index;
}

/// [i, j)
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Bounds(pub(crate) u64, pub(crate) u64);

pub trait IntoBounds: private::Sealed {
    fn into_bounds(self, bit_size: u64) -> Bounds;
}

impl From<Bounds> for Index {
    #[inline(always)]
    fn from(Bounds(i, j): Bounds) -> Index {
        Index::Range(i, j)
    }
}

impl Bounds {
    #[allow(clippy::range_plus_one)]
    #[rustfmt::skip]
    pub(crate) fn bounds<R: std::fmt::Debug+ops::RangeBounds<u64>>(range: &R, size: u64) -> Bounds {
        use std::ops::Bound::*;
        match (range.start_bound(), range.end_bound()) {
            (Included(&i), Included(&j)) if i   < size && i <= j && j <  size => Bounds(i  , j+1),
            (Included(&i), Excluded(&j)) if i   < size && i <= j && j <= size => Bounds(i  , j  ),
            (Excluded(&i), Included(&j)) if i+1 < size && i <  j && j <  size => Bounds(i+1, j+1),
            (Excluded(&i), Excluded(&j)) if i+1 < size && i <  j && j <= size => Bounds(i+1, j  ),
            (Included(&i), Unbounded)    if i   < size                        => Bounds(i  , size),
            (Excluded(&i), Unbounded)    if i+1 < size                        => Bounds(i+1, size),
            (Unbounded,    Included(&j)) if                         j <  size => Bounds(0  , j+1),
            (Unbounded,    Excluded(&j)) if                         j <= size => Bounds(0  , j  ),
            (Unbounded,    Unbounded)                                         => Bounds(0  , size),
            _ => panic!("unexpected range"),
        }
    }

    #[inline(always)]
    fn len(&self) -> u64 {
        let Bounds(i, j) = self;
        j - i
    }
}

impl crate::private::Sealed for Index {}
impl IntoIndex for Index {
    #[inline(always)]
    fn into_bit(self, _: u64) -> Index {
        self
    }
}

impl crate::private::Sealed for Bounds {}
impl IntoBounds for Bounds {
    #[inline(always)]
    fn into_bounds(self, _: u64) -> Bounds {
        self
    }
}

impl IntoIndex for u64 {
    #[inline(always)]
    fn into_bit(self, bit_size: u64) -> Index {
        assert!(self < bit_size);
        Index::Exact(self)
    }
}
impl IntoBounds for u64 {
    #[inline(always)]
    fn into_bounds(self, bit_size: u64) -> Bounds {
        assert!(self <= bit_size);
        Bounds(0, self)
    }
}

macro_rules! implRangeVariants {
    ( $( $Type:ty ),* ) => ($(
        impl crate::private::Sealed for $Type {}
        impl IntoIndex for $Type {
            fn into_bit(self, bit_size: u64) -> Index {
                Index::from(Bounds::bounds(&self, bit_size))
            }
        }
        impl IntoBounds for $Type {
            fn into_bounds(self, bit_size: u64) -> Bounds {
                Bounds::bounds(&self, bit_size)
            }
        }
    )*)
}
macro_rules! implRangeRefVariants {
    ( $( $Type:ty ),* ) => ($(
        impl<'a> crate::private::Sealed for $Type {}

        impl<'a> IntoIndex for $Type {
            #[inline]
            fn into_bit(self, bit_size: u64) -> Index {
                Index::from(Bounds::bounds(&self, bit_size))
            }
        }
        impl<'a> IntoBounds for $Type {
            #[inline]
            fn into_bounds(self, bit_size: u64) -> Bounds {
                Bounds::bounds(&self, bit_size)
            }
        }
    )*)
}

implRangeVariants!(
    ops::Range<u64>,
    ops::RangeFrom<u64>,
    ops::RangeInclusive<u64>,
    ops::RangeTo<u64>,
    ops::RangeToInclusive<u64>,
    (ops::Bound<u64>, ops::Bound<u64>),
    ops::RangeFull
);
implRangeRefVariants!(
    ops::Range<&'a u64>,
    ops::RangeFrom<&'a u64>,
    ops::RangeInclusive<&'a u64>,
    ops::RangeTo<&'a u64>,
    ops::RangeToInclusive<&'a u64>,
    (ops::Bound<&'a u64>, ops::Bound<&'a u64>)
);

/// `Indexs` denotes types with a finite, constant number of bit.
///
/// This trait is for types intended to use as a component of the bit container.
pub trait Bits:
    Clone + BitCount + BitGet + BitPut + BitRank + BitSelect1 + BitSelect0 + crate::private::Sealed
{
    /// The potential bit size.
    ///
    /// This constant value corresponds to total of enabled/disabled bit.
    const SIZE: u64;

    /// Returns an empty bit block.
    ///
    /// The number of disabled bit of an empty instance must be equal to `SIZE`.
    fn empty() -> Self;
}

/// `Count` is a trait that counts the number of enabled/disabled bit in the container.
///
/// Every method have a cycled default implementations.
/// At least two methods need be re-defined.
pub trait BitCount {
    /// The value corresponds to total of enabled/disabled bit.
    /// Defined as `count1 + count0`.
    fn size(&self) -> u64 {
        self.count1() + self.count0()
    }

    /// Return the number of enabled bit in the container. Defined as `bit - count0`.
    /// The order of counting bit depends on the implementation.
    fn count1(&self) -> u64 {
        self.size() - self.count0()
    }

    /// Return the number of disabled bit in the container. Defined as `bit - count1`.
    /// The order of counting bit depends on the implementation.
    fn count0(&self) -> u64 {
        self.size() - self.count1()
    }
}

pub trait BitGet: BitCount {
    /// Reads `n` bits from `[i, i+n)`, and returns them as the lowest n bit of `W`.
    ///
    /// # Panics
    ///
    /// Panics if bit size of `n` does not fit in `W` or either `i` or `i + n` is out of bounds.
    fn bits<W: Word>(&self, i: u64, n: u64) -> W;

    /// Checks bit at `i`.
    ///
    /// This method can be derived from `bits`, but in most cases
    /// it's better to re-define with the more specialized implementation.
    #[inline]
    fn bit(&self, i: u64) -> bool {
        self.bits::<u8>(i, 1) == 1
    }

    /// Reads a byte from `[i, i+8)`.
    #[inline]
    fn byte(&self, i: u64) -> u8 {
        self.bits::<u8>(i, 8)
    }

    /// Return the positions of all enabled bit in the container.
    ///
    /// Default implementation is just a accessing to all bit.
    fn ones<'a>(&'a self) -> Box<dyn Iterator<Item = u64> + 'a> {
        Box::new((0..self.size()).filter(move |&i| self.bit(i)))
    }
}

pub trait BitPut: BitGet {
    /// Enables the bit at `i`, and returns the number of inserted bit.
    fn put1(&mut self, i: u64) -> u64;

    /// Disables the bit at `i`, and returns the number of removed bit.
    fn put0(&mut self, i: u64) -> u64;

    /// Writes the `n` lowest bit of the bits `w`.
    ///
    /// # Panics
    ///
    /// Panics if `n` does not fit in bit size of `W` or either `i` or `i+n` is out of bounds.
    fn puts<W: Word>(&mut self, i: u64, n: u64, w: W) {
        for j in 0..n {
            if w.bit(j) {
                self.put1(i + j);
            } else {
                self.put0(i + j);
            }
        }
    }

    /// Enables the bit/bits.
    ///
    /// ```
    /// use compacts::bit::ops::{BitCount, BitPut};
    /// let mut vec = vec![0u8; 8];
    /// vec.set1(..);
    /// assert_eq!(vec.count1(), 64);
    /// vec.set0(..);
    /// assert_eq!(vec.count1(), 0);
    /// vec.set1(2..=2);
    /// assert_eq!(vec.count1(), 1);
    /// vec.set1(0..50);
    /// vec.set0(2..=30);
    /// assert_eq!(vec.count1(), 21);
    /// ```
    fn set1<Ix: IntoIndex>(&mut self, index: Ix) {
        match index.into_bit(self.size()) {
            Index::Exact(i) => {
                self.put1(i);
            }
            Index::Range(i, j) => {
                bit::ix_len(i, j, u64::SIZE).for_each(|(n, len)| self.puts::<u64>(n, len, !0));
            }
        }
    }

    /// Disables the bit/bits.
    fn set0<Ix: IntoIndex>(&mut self, index: Ix) {
        match index.into_bit(self.size()) {
            Index::Exact(i) => {
                self.put0(i);
            }
            Index::Range(i, j) => {
                bit::ix_len(i, j, u64::SIZE).for_each(|(n, len)| self.puts::<u64>(n, len, 0));
            }
        }
    }

    /// Flips the bit.
    ///
    /// ```
    /// use compacts::bit::ops::BitPut;
    /// let mut vec = vec![0u8; 10];
    /// vec.flip(1);
    /// vec.flip(10..80);
    /// assert_eq!(vec, vec![
    ///     0b00000010, 0b11111100, 0b11111111, 0b11111111, 0b11111111,
    ///     0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111,
    /// ]);
    /// vec.flip(20..64);
    /// assert_eq!(vec, vec![
    ///     0b00000010, 0b11111100, 0b00001111, 0b00000000, 0b00000000,
    ///     0b00000000, 0b00000000, 0b00000000, 0b11111111, 0b11111111,
    /// ]);
    /// vec.flip(0..77);
    /// assert_eq!(vec, vec![
    ///     0b11111101, 0b00000011, 0b11110000, 0b11111111, 0b11111111,
    ///     0b11111111, 0b11111111, 0b11111111, 0b00000000, 0b11100000,
    /// ]);
    /// ```
    fn flip<Ix: IntoIndex>(&mut self, index: Ix) {
        match index.into_bit(self.size()) {
            Index::Exact(i) => {
                if self.bit(i) {
                    self.put0(i);
                } else {
                    self.put1(i);
                }
            }
            Index::Range(i, j) => bit::ix_len(i, j, u64::SIZE).for_each(|(n, len)| {
                self.puts::<u64>(n, len, !self.bits::<u64>(n, len));
            }),
        }
    }
}

/// `Rank1` is a generization of `Count`.
pub trait BitRank: BitCount {
    /// Returns the number of enabled bit in the given bounds.
    fn rank1<Ix: IntoBounds>(&self, index: Ix) -> u64 {
        let size = self.size();
        match index.into_bounds(size) {
            Bounds(0, i) => {
                if i == size {
                    self.count1()
                } else {
                    i - self.rank0(i)
                }
            }
            b @ Bounds(_, _) => b.len() - self.rank0(b),
        }
    }

    /// Returns the number of disabled bit in the given bounds.
    fn rank0<Ix: IntoBounds>(&self, index: Ix) -> u64 {
        let size = self.size();
        match index.into_bounds(size) {
            Bounds(0, i) => {
                if i == size {
                    self.count0()
                } else {
                    i - self.rank1(i)
                }
            }
            b @ Bounds(_, _) => b.len() - self.rank1(b),
        }
    }

    /// Returns the nth occurences of `1`.
    fn search1(&self, n: u64) -> Option<u64> {
        if n < self.count1() {
            let i = 0;
            let j = cast(self.size());
            Some(search_index(i, j, |k| self.rank1(Bounds(0, k)) > n) - 1)
        } else {
            None
        }
    }

    /// Returns the nth occurences of `0`.
    fn search0(&self, n: u64) -> Option<u64> {
        if n < self.count0() {
            let i = 0;
            let j = cast(self.size());
            Some(search_index(i, j, |k| self.rank0(Bounds(0, k)) > n) - 1)
        } else {
            None
        }
    }
}

/// Right inverse of `rank1`.
pub trait BitSelect1: BitRank {
    /// Default implementation is derived from `BitRank`.
    fn select1(&self, rank: u64) -> Option<u64> {
        self.search1(rank)
    }
}

/// Right inverse of `rank0`.
pub trait BitSelect0: BitRank {
    /// Default implementation is derived from `BitSearch0`.
    fn select0(&self, rank: u64) -> Option<u64> {
        self.search0(rank)
    }
}

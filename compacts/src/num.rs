use crate::{bit::ops::*, bit::OUT_OF_BOUNDS, private};
use std::ops;

/// Trait for an unsigned int. This trait is public but sealed.
pub trait Word:
    'static
    + Copy
    + Eq
    + Ord
    + Default
    + std::fmt::Debug
    + std::hash::Hash
    + ops::Add<Output = Self>
    + ops::Sub<Output = Self>
    + ops::Mul<Output = Self>
    + ops::Div<Output = Self>
    + ops::Rem<Output = Self>
    + ops::Shl<Output = Self>
    + ops::Shr<Output = Self>
    + ops::BitAnd<Output = Self>
    + ops::BitOr<Output = Self>
    + ops::BitXor<Output = Self>
    + ops::Not<Output = Self>
    + ops::AddAssign
    + ops::SubAssign
    + ops::MulAssign
    + ops::DivAssign
    + ops::RemAssign
    + ops::ShlAssign
    + ops::ShrAssign
    + ops::BitAndAssign
    + ops::BitOrAssign
    + ops::BitXorAssign
    + std::iter::Sum
    + TryCast<u8>
    + TryCast<u16>
    + TryCast<u32>
    + TryCast<u64>
    + TryCast<u128>
    + TryCast<usize>
    + TryCastFrom<u8>
    + TryCastFrom<u16>
    + TryCastFrom<u32>
    + TryCastFrom<u64>
    + TryCastFrom<u128>
    + TryCastFrom<usize>
    + Bits
    + private::Sealed
{
    const MIN: Self;
    const MAX: Self;

    const ONE: Self;
    const TWO: Self;

    fn mask<T: Word + TryCast<Self>>(i: T) -> Self {
        let i = cast(i);
        if Self::SIZE == i {
            !Self::MIN
        } else {
            Self::ONE.shiftl(i) - Self::ONE
        }
    }

    /// Equals to `wrapping_shl`.
    #[doc(hidden)]
    fn shiftl<T: Word + TryCast<Self>>(&self, i: T) -> Self;
    /// Equals to `wrapping_shr`.
    #[doc(hidden)]
    fn shiftr<T: Word + TryCast<Self>>(&self, i: T) -> Self;

    #[doc(hidden)]
    #[inline(always)]
    fn div2(self) -> Self {
        self / (Self::ONE + Self::ONE)
    }
}

/// Lossless cast that never fail.
pub trait Cast<T>: crate::private::Sealed {
    fn cast(self) -> T;
}

/// Lossless cast that may fail.
pub trait TryCast<T>: crate::private::Sealed {
    fn try_cast(self) -> Option<T>;
}

/// Lossless cast that never fail.
pub trait CastFrom<T>: Sized + crate::private::Sealed {
    fn cast_from(from: T) -> Self;
}

/// Lossless cast that may fail.
pub trait TryCastFrom<T>: Sized + crate::private::Sealed {
    fn try_cast_from(from: T) -> Option<Self>;
}

impl<T: Word> CastFrom<T> for T {
    fn cast_from(from: T) -> T {
        from
    }
}
impl<T: Word, U: CastFrom<T>> TryCastFrom<T> for U {
    fn try_cast_from(from: T) -> Option<Self> {
        Some(U::cast_from(from))
    }
}

impl<T: Word, U: CastFrom<T>> Cast<U> for T {
    fn cast(self) -> U {
        U::cast_from(self)
    }
}

impl<T: Word, U: TryCastFrom<T>> TryCast<U> for T {
    fn try_cast(self) -> Option<U> {
        U::try_cast_from(self)
    }
}

/// Cast U into T.
///
/// # Panics
///
/// Panics if given `u` does not fit in `T`.
#[inline]
pub fn cast<U, T>(u: U) -> T
where
    U: Word + TryCast<T>,
    T: Word,
{
    u.try_cast().expect("does not fit in T")
}

#[inline]
pub fn divrem<U: Word>(i: u64, cap: u64) -> (U, u64)
where
    u64: TryCast<U>,
{
    (cast(i / cap), i % cap)
}

pub fn search_index<T: Word>(mut i: T, mut j: T, func: impl Fn(T) -> bool) -> T {
    assert!(i < j);
    while i < j {
        let h = i + (j - i) / T::TWO;
        if func(h) {
            j = h; // f(j) == true
        } else {
            i = h + T::ONE; // f(i-1) == false
        }
    }
    i // f(i-1) == false && f(i) (= f(j)) == true
}

#[test]
fn test_search_index() {
    let vec = [0, 100, 100, 400];
    assert_eq!(search_index(0, vec.len(), |i| vec[i] >= 100), 1);
    assert_eq!(search_index(0, vec.len(), |i| vec[i] >= 300), 3);
    assert_eq!(search_index(0, vec.len(), |i| vec[i] >= 400), 3);
    assert_eq!(search_index(0, vec.len(), |i| vec[i] >= 500), 4);
    assert_eq!(search_index(0, vec.len(), |i| vec[i] > 100), 3);
    assert_eq!(search_index(0, vec.len(), |i| vec[i] > 300), 3);
    assert_eq!(search_index(0, vec.len(), |i| vec[i] > 400), 4);
    assert_eq!(search_index(0, vec.len(), |i| vec[i] > 500), 4);
}

macro_rules! implWord {
    ($($ty:ty),*) => ($(
        impl Word for $ty {
            const MIN: Self = 0;
            const MAX: Self = !0;

            const ONE: Self = 1;
            const TWO: Self = 2;

            fn shiftl<T>(&self, i: T) -> Self where T: Word + TryCast<Self> {
                self.wrapping_shl(cast(i))
            }
            fn shiftr<T>(&self, i: T) -> Self where T: Word + TryCast<Self> {
                self.wrapping_shr(cast(i))
            }
        }
    )*)
}
implWord!(u8, u16, u32, u64, u128, usize);

macro_rules! implCastFrom {
    ( $large:ty; $( $small:ty ),* ) => ($(
        impl CastFrom<$small> for $large {
            #[allow(clippy::cast_lossless)]
            #[inline]
            fn cast_from(from: $small) -> $large {
                from as $large
            }
        }
    )*)
}
implCastFrom!(u128; u8, u16, u32, u64);
implCastFrom!( u64; u8, u16, u32);
implCastFrom!( u32; u8, u16);
implCastFrom!( u16; u8);

#[cfg(target_pointer_width = "32")]
mod cast_from_for_usize {
    use super::*;
    implCastFrom!(usize; u8, u16, u32);
    implCastFrom!(u128; usize);
    implCastFrom!( u64; usize);
    implCastFrom!( u32; usize);
}
#[cfg(target_pointer_width = "64")]
mod cast_from_for_usize {
    use super::*;
    implCastFrom!(usize; u8, u16, u32, u64);
    implCastFrom!(u128; usize);
    implCastFrom!( u64; usize);
}

macro_rules! implTryCastFrom {
    ( $small:ty; $( $large:ty ),* ) => ($(
        impl TryCastFrom<$large> for $small {
            #[allow(clippy::cast_lossless)]
            #[inline]
            fn try_cast_from(from: $large) -> Option<$small> {
                const MIN: $small = 0;
                const MAX: $small = !MIN;
                if from <= MAX as $large {
                    Some(from as $small)
                } else {
                    None
                }
            }
        }
    )*)
}
implTryCastFrom!(u64; u128);
implTryCastFrom!(u32; u128, u64);
implTryCastFrom!(u16; u128, u64, u32);
implTryCastFrom!( u8; u128, u64, u32, u16);

#[cfg(target_pointer_width = "32")]
mod try_cast_from_for_usize {
    use super::*;
    implTryCastFrom!(usize; u128);
    implTryCastFrom!(u16; usize);
    implTryCastFrom!( u8; usize);
}
#[cfg(target_pointer_width = "64")]
mod try_cast_from_for_usize {
    use super::*;
    implTryCastFrom!(usize; u128);
    implTryCastFrom!(u32; usize);
    implTryCastFrom!(u16; usize);
    implTryCastFrom!( u8; usize);
}

macro_rules! impls {
    ($($ty:ty),*) => ($(
        impl Bits for $ty {
            #[allow(clippy::cast_lossless)]
            const SIZE: u64 = std::mem::size_of::<$ty>() as u64 * 8;
            #[inline]
            fn empty() -> Self { 0 }
        }

        impl BitCount for $ty {
            #[inline]
            fn size(&self) -> u64 {
                Self::SIZE
            }
            #[inline]
            fn count1(&self) -> u64 {
                u64::from(self.count_ones())
            }
            #[inline]
            fn count0(&self) -> u64 {
                u64::from(self.count_zeros())
            }
        }

        impl BitGet for $ty {
            fn bits<W: Word>(&self, i: u64, len: u64) -> W {
                assert!(len <= W::SIZE && i < self.size() && i + len <= self.size(), OUT_OF_BOUNDS);
                match (i, i + len) {
                    (n, m) if n == m => W::MIN,
                    (n, m) => {
                        let mask = (!0).shiftl(n) & (!0).shiftr(Self::SIZE - m);
                        cast::<$ty, W>((*self & mask).shiftr(i))
                    },
                }
            }

            #[inline]
            fn bit(&self, i: u64) -> bool {
                (*self & Self::ONE.shiftl(i)) != Self::MIN
            }
        }

        impl BitPut for $ty {
            fn puts<W: Word>(&mut self, i: u64, len: u64, num: W) {
                assert!(len <= W::SIZE && i < Self::SIZE && i + len <= Self::SIZE, OUT_OF_BOUNDS);
                let umask = <Self as Word>::mask(len);
                let smask = umask.shiftl(i);
                // let prev = (*self & smask).shiftr(i);
                *self &= !smask;
                *self |= cast::<W, Self>(num & W::mask(len)).shiftl(i);
                // return cast::<Self, W>(prev);
            }

            #[inline]
            fn put1(&mut self, i: u64) -> u64 {
                assert!(i < Self::SIZE, OUT_OF_BOUNDS);
                let old = self.count1();
                *self |= Self::ONE.shiftl(i);
                self.count1() - old
            }

            #[inline]
            fn put0(&mut self, i: u64) -> u64 {
                assert!(i < Self::SIZE, OUT_OF_BOUNDS);
                let old = self.count1();
                *self &= !Self::ONE.shiftl(i);
                old - self.count1()
            }
        }

        impl BitRank for $ty {
            fn rank1<Ix: IntoBounds>(&self, r: Ix) -> u64 {
                let rank = |i| {
                    if i == Self::SIZE {
                        self.count1()
                    } else {
                        (*self & Self::mask(i)).count1()
                    }
                };
                match r.into_bounds(Self::SIZE) {
                    Bounds(0, i) => rank(i),
                    Bounds(i, j) => rank(j) - rank(i)
                }
            }
        }
    )*)
}
impls!(u8, u16, u32, u64, u128, usize);

const X01: u64 = 0x0101_0101_0101_0101;
const X02: u64 = 0x2020_2020_2020_2020;
const X33: u64 = 0x3333_3333_3333_3333;
const X22: u64 = 0x2222_2222_2222_2222;
const X80: u64 = 0x2010_0804_0201_0080;
const X81: u64 = 0x2010_0804_0201_0081;
const X0F: u64 = 0x0f0f_0f0f_0f0f_0f0f;
const X55: u64 = X22 + X33 + X22 + X33;
const X8X: u64 = X81 + X80 + X80 + X80;

#[inline]
const fn le8(x: u64, y: u64) -> u64 {
    let x8 = X02 + X02 + X02 + X02;
    let xs = (y | x8) - (x & !x8);
    (xs ^ x ^ y) & x8
}

#[inline]
const fn lt8(x: u64, y: u64) -> u64 {
    let x8 = X02 + X02 + X02 + X02;
    let xs = (x | x8) - (y & !x8);
    (xs ^ x ^ !y) & x8
}

impl BitSelect1 for u64 {
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::ops::{BitRank, BitSelect1};
    /// let n = 0b_00000100_10010000_u64;
    /// assert_eq!(n.select1(0), Some(4));
    /// assert_eq!(n.select1(1), Some(7));
    /// assert_eq!(n.select1(2), Some(10));
    /// assert_eq!(n.select1(3), None);
    /// assert_eq!(n.rank1(..n.select1(0).unwrap()), 0);
    /// assert_eq!(n.rank1(..n.select1(1).unwrap()), 1);
    /// assert_eq!(n.rank1(..n.select1(2).unwrap()), 2);
    /// ```
    #[allow(clippy::cast_lossless)]
    fn select1(&self, c: u64) -> Option<u64> {
        if c < self.count1() {
            let x = self;
            let s0 = x - ((x & X55) >> 1);
            let s1 = (s0 & X33) + ((s0 >> 2) & X33);
            let s2 = ((s1 + (s1 >> 4)) & X0F).wrapping_mul(X01);
            let p0 = (le8(s2, c * X01) >> 7).wrapping_mul(X01);
            let p1 = (p0 >> 53) & !0x7;
            let p2 = p1 as u32;
            let p3 = (s2 << 8).wrapping_shr(p2);
            let p4 = c - (p3 & 0xFF);
            let p5 = lt8(0x0, ((x.wrapping_shr(p2) & 0xFF) * X01) & X8X);
            let s3 = (p5 >> 0x7).wrapping_mul(X01);
            let p6 = (le8(s3, p4 * X01) >> 7).wrapping_mul(X01) >> 56;
            let p7 = p1 + p6;
            assert!(p7 < Self::SIZE);
            Some(p7)
        } else {
            None
        }
    }
}

impl BitSelect1 for u128 {
    fn select1(&self, mut c: u64) -> Option<u64> {
        let hi = (*self >> 64) as u64;
        let lo = *self as u64;
        if c < lo.count1() {
            return lo.select1(c);
        }
        c -= lo.count1();
        hi.select1(c).map(|x| x + 64)
    }
}

macro_rules! implSelect1 {
    ( $( $ty:ty ),* ) => ($(
        impl BitSelect1 for $ty {
            #[allow(clippy::cast_lossless)]
            #[inline]
            fn select1(&self, c: u64) -> Option<u64> {
                if c < self.count1() {
                    (*self as u64).select1(c)
                } else {
                    None
                }
            }
        }
    )*)
}
macro_rules! implSelect0 {
    ($($ty:ty),*) => ($(
        impl BitSelect0 for $ty {
            #[inline]
            fn select0(&self, c: u64) -> Option<u64> {
                if c < self.count0() {
                    (!self).select1(c)
                } else {
                    None
                }
            }
        }
    )*)
}
implSelect1!(u8, u16, u32, usize);
implSelect0!(u8, u16, u32, u64, u128, usize);

/// Word array.
pub trait Words: 'static + Copy + Bits {
    /// Type of element.
    type Word: Word;

    const LEN: usize;

    /// [value; LEN]
    fn splat(value: Self::Word) -> Self;

    fn as_slice(&self) -> &[Self::Word];
    fn as_slice_mut(&mut self) -> &mut [Self::Word];
}

// FIXME: Revisit here when const generics is stabilized.
// `[T; N]` is almost same with `[T]` where T is an Word, except that `[T; N]` implements `Bits`.
macro_rules! implWords {
    ($( ($Word:ty, $LEN:expr) ),*) => ($(
        impl crate::private::Sealed for [$Word; $LEN] {}

        impl Words for [$Word; $LEN] {
            type Word = $Word;
            const LEN: usize = $LEN;

            fn splat(bits: Self::Word) -> Self              { [bits; $LEN] }
            fn as_slice(&self)         -> &[Self::Word]     { &self[..] }
            fn as_slice_mut(&mut self) -> &mut [Self::Word] { &mut self[..] }
        }

        impl Bits for [$Word; $LEN] {
            const SIZE: u64 = $LEN as u64 * <$Word as Bits>::SIZE;
            fn empty() -> Self {
                Self::splat(0)
            }
        }

        impl BitCount for [$Word; $LEN] {
            fn size(&self) -> u64 {
                Self::SIZE
            }
            fn count1(&self) -> u64 {
                self.as_slice().count1()
            }
        }

        impl BitGet for [$Word; $LEN] {
            fn bits<W: Word>(&self, i: u64, len: u64) -> W {
                self.as_slice().bits(i, len)
            }
            fn bit(&self, i: u64) -> bool {
                self.as_slice().bit(i)
            }
            fn ones<'a>(&'a self) -> Box<dyn Iterator<Item = u64> + 'a> {
                self.as_slice().ones()
            }
        }

        impl BitPut for [$Word; $LEN] {
            fn puts<W: Word>(&mut self, i: u64, len: u64, w: W) {
                self.as_slice_mut().puts(i, len, w)
            }
            fn put1(&mut self, i: u64) -> u64 {
                self.as_slice_mut().put1(i)
            }
            fn put0(&mut self, i: u64) -> u64 {
                self.as_slice_mut().put0(i)
            }
        }

        impl BitRank for [$Word; $LEN] {
            fn rank1<Ix: IntoBounds>(&self, r: Ix) -> u64 {
                self.as_slice().rank1(r)
            }
        }

        impl BitSelect1 for [$Word; $LEN] {
            fn select1(&self, n: u64) -> Option<u64> {
                self.as_slice().select1(n)
            }
        }
        impl BitSelect0 for [$Word; $LEN] {
            fn select0(&self, n: u64) -> Option<u64> {
                self.as_slice().select0(n)
            }
        }
    )*)
}

#[rustfmt::skip]
implWords!(
    (u8,   8192),
    (u16,  4096),
    (u32,  2048),
    (u64,  1024),
    (u128,  512)
);

#[cfg(target_pointer_width = "32")]
implWords!((usize, 2048));
#[cfg(target_pointer_width = "64")]
implWords!((usize, 1024));

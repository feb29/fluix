use crate::{
    bit::ops::*,
    bit::MAX_SIZE,
    num::{cast, Word},
};

use std::ops::{Index, IndexMut};

/// A deadly simple bit sequence.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Seq<T = u64>(pub(crate) Vec<T>);

impl<T> AsRef<[T]> for Seq<T> {
    fn as_ref(&self) -> &[T] {
        &self.0[..]
    }
}
impl<T> AsMut<[T]> for Seq<T> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.0[..]
    }
}

impl<T, Idx> Index<Idx> for Seq<T>
where
    Vec<T>: Index<Idx>,
{
    type Output = <Vec<T> as Index<Idx>>::Output;
    fn index(&self, i: Idx) -> &Self::Output {
        &self.0[i]
    }
}
impl<T, Idx> IndexMut<Idx> for Seq<T>
where
    Vec<T>: IndexMut<Idx>,
{
    fn index_mut(&mut self, i: Idx) -> &mut Self::Output {
        &mut self.0[i]
    }
}

impl<T> Seq<T> {
    pub fn new() -> Self {
        Seq(Vec::new())
    }

    pub fn with_capacity(cap: usize) -> Self {
        Seq(Vec::with_capacity(cap))
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    #[inline]
    pub fn truncate(&mut self, n: usize) {
        self.0.truncate(n)
    }
}

pub(crate) struct Runs<'a, T> {
    iter: std::iter::Peekable<std::slice::Iter<'a, T>>,
}

impl<T: Word> Iterator for Runs<'_, T> {
    type Item = std::ops::RangeInclusive<T>;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().and_then(|&n| {
            let mut m = n;
            while let Some(&peek) = self.iter.peek() {
                if m + T::ONE == *peek {
                    m = *peek;
                    self.iter.next();
                    continue;
                } else {
                    break;
                }
            }
            Some(n..=m)
        })
    }
}

impl<T: Word> Seq<T> {
    #[inline]
    pub fn of(mut data: Vec<T>) -> Self
    where
        T: Word,
    {
        data.dedup();
        data.sort_unstable();
        Seq(data)
    }

    #[inline]
    fn search(&self, bit: T) -> Result<usize, usize>
    where
        T: Word,
    {
        self.0.binary_search(&bit)
    }

    pub(crate) fn runs(&self) -> Runs<'_, T> {
        Runs {
            iter: self.0.iter().peekable(),
        }
    }
}

// impl<T> crate::private::Sealed for Seq<T> {}
// impl<T: Word> Bits for Seq<T> {
//     const SIZE: u64 = 1 << T::SIZE;
//     fn empty() -> Self {
//         Self::new()
//     }
// }

impl<T: Word> BitCount for Seq<T> {
    fn size(&self) -> u64 {
        1u64.checked_shl(T::SIZE as u32).unwrap_or(MAX_SIZE)
    }
    fn count1(&self) -> u64 {
        self.len() as u64
    }
}

impl<T: Word> BitGet for Seq<T> {
    /// # Examples
    ///
    /// ```
    /// use compacts::bit::{self, ops::BitGet};
    /// let seq = bit::Seq::of(vec![65534u64, 65535, 65536, 65537, 131071]);
    /// assert_eq!(seq.bits::<u64>(     0, 64), 0b_0000_0000);
    /// assert_eq!(seq.bits::<u64>(    64, 64), 0b_0000_0000);
    /// assert_eq!(seq.bits::<u64>( 65530, 60), 0b_1111_0000);
    /// assert_eq!(seq.bits::<u64>( 65534, 16), 0b_0000_1111);
    /// assert_eq!(seq.bits::<u64>( 65535, 63), 0b_0000_0111);
    /// assert_eq!(seq.bits::<u64>( 65536, 63), 0b_0000_0011);
    /// assert_eq!(seq.bits::<u64>(131071,  1), 0b_0000_0001);
    ///
    /// assert_eq!(seq.bits::<u64>( 65533,  0), 0b_0000_0000);
    /// assert_eq!(seq.bits::<u64>( 65534,  0), 0b_0000_0000);
    /// assert_eq!(seq.bits::<u64>( 65534,  3), 0b_0000_0111);
    /// ```
    fn bits<W: Word>(&self, i: u64, len: u64) -> W {
        assert!(len <= W::SIZE && i < self.size() && i + len <= self.size());
        if len == 0 {
            return W::MIN;
        }

        match self.search(cast(i)) {
            Ok(index) if index + 1 < self.0.len() => {
                let mut out = W::ONE;
                for &b in self.0[index + 1..]
                    .iter()
                    .take_while(|&x| cast::<T, u64>(*x) < i + len)
                {
                    let next = cast::<T, u64>(b);
                    out.put1(next - i);
                }
                out
            }
            Err(index) if index < self.0.len() => {
                let mut out = W::MIN;
                for &b in self.0[index..]
                    .iter()
                    .take_while(|&x| cast::<T, u64>(*x) < i + len)
                {
                    let next = cast::<T, u64>(b);
                    out.put1(next - i);
                }
                out
            }

            Ok(index) if index + 1 >= self.0.len() => W::ONE,
            Err(index) if index >= self.0.len() => W::MIN,
            _ => unreachable!(),
        }
    }

    fn bit(&self, i: u64) -> bool {
        self.search(cast(i)).is_ok()
    }
    fn ones<'a>(&'a self) -> Box<dyn Iterator<Item = u64> + 'a> {
        Box::new(self.0.iter().map(|&i| cast::<T, u64>(i)))
    }
}

impl<T: Word> BitPut for Seq<T> {
    fn put1(&mut self, i: u64) -> u64 {
        assert!(i < self.size());
        let i = cast::<u64, T>(i);
        if let Err(loc) = self.search(i) {
            self.0.insert(loc, i);
            1
        } else {
            0
        }
    }

    fn put0(&mut self, i: u64) -> u64 {
        assert!(i < self.size());
        let i = cast::<u64, T>(i);
        if let Ok(loc) = self.search(i) {
            self.0.remove(loc);
            1
        } else {
            0
        }
    }

    /// ```
    /// use compacts::{bit, bit::ops::BitPut};
    /// let mut seq = bit::Seq::<u64>::new();
    /// seq.puts::<u8>( 3, 2, 0b10);
    /// seq.puts::<u8>( 2, 3, 0b011);
    /// seq.puts::<u8>( 8, 3, 0b101);
    /// seq.puts::<u8>( 7, 4, 0b1111);
    /// seq.puts::<u8>(16, 4, 0b1001);
    /// assert_eq!(seq, bit::Seq::of(vec![2, 3, 7, 8, 9, 10, 16, 19]));
    /// ```
    fn puts<W: Word>(&mut self, i: u64, len: u64, w: W) {
        assert!(len <= W::SIZE && i < self.size() && i + len <= self.size());
        for k in 0..len {
            let b = i + k;
            if w.bit(k) {
                self.put1(b);
            } else {
                self.put0(b);
            }
        }
    }
}

impl<T: Word> BitRank for Seq<T> {
    /// Returns the number of enabled bit in `[0, i)`.
    ///
    /// ```
    /// use compacts::bit::{Seq, ops::{BitCount, BitRank}};
    /// let seq = Seq::of(vec![13u16, 14, 20]);
    /// assert_eq!(seq.rank1(10), 0);
    /// assert_eq!(seq.rank1(14), 1);
    /// assert_eq!(seq.rank1(16), 2);
    ///
    /// assert_eq!(seq.rank1(10..10), 0);
    /// assert_eq!(seq.rank1(10..14), 1);
    /// assert_eq!(seq.rank1(  ..20), 2);
    /// ```
    fn rank1<Ix: IntoBounds>(&self, index: Ix) -> u64 {
        let rank = |p| {
            // Search the smallest index `p` that satisfy `vec[p] >= i`,
            // `k` also implies the number of enabled bit in [0, p).
            // For example, searching 5 in `[0, 1, 7]` return 2.
            cast::<usize, u64>(match self.search(cast(p)) {
                Ok(p) | Err(p) => p,
            })
        };

        match index.into_bounds(self.size()) {
            Bounds(i, j) if i == j => 0,
            Bounds(0, i) if i == self.size() => self.count1(),
            Bounds(0, i) => rank(i),
            Bounds(i, j) if j == self.size() => self.count1() - rank(i),
            Bounds(i, j) => rank(j) - rank(i),
        }
    }
}

impl<T: Word> BitSelect1 for Seq<T> {
    /// ```
    /// use compacts::bit::{Seq, ops::{BitCount, BitSelect1, BitSelect0}};
    /// let seq = Seq::of(vec![0u64, 3, 13, 14, 20]);
    /// assert_eq!(seq.select1(0), Some( 0));
    /// assert_eq!(seq.select1(1), Some( 3));
    /// assert_eq!(seq.select1(2), Some(13));
    /// assert_eq!(seq.select1(3), Some(14));
    /// assert_eq!(seq.select1(4), Some(20));
    /// assert_eq!(seq.select1(5), None);
    ///
    /// let seq = Seq::of(vec![0u64, 3, 6, 8]);
    /// assert_eq!(seq.select0(0), Some(1));
    /// assert_eq!(seq.select0(1), Some(2));
    /// assert_eq!(seq.select0(2), Some(4));
    /// assert_eq!(seq.select0(3), Some(5));
    /// assert_eq!(seq.select0(4), Some(7));
    /// assert_eq!(seq.select0(5), Some(9));
    /// ```
    fn select1(&self, n: u64) -> Option<u64> {
        self.0.get(cast::<u64, usize>(n)).map(|&x| cast(x))
    }
}
impl<T: Word> BitSelect0 for Seq<T> {
    fn select0(&self, c: u64) -> Option<u64> {
        self.search0(c)
    }
}

// impl<T: Word> Seq<T> {
//     fn intersection<'a>(&'a self, rhs: &'a Seq<T>) -> impl Iterator<Item = &'a T> + 'a {
//         let members = Intersection {
//             a: self.0.iter().peekable(),
//             b: rhs.0.iter().peekable(),
//         };
//         members.filter_map(|member| match member {
//             Member::And { lhs, rhs: _ } => Some(lhs),
//             _ => None,
//         })
//     }

//     fn union<'a>(&'a mut self, rhs: &'a Seq<T>) -> impl Iterator<Item = &'a T> + 'a {
//         let members = Union {
//             a: self.0.iter().peekable(),
//             b: rhs.0.iter().peekable(),
//         };
//         members.map(|member| match member {
//             Member::And { lhs, rhs: _ } => lhs,
//             Member::Lhs(lhs) => lhs,
//             Member::Rhs(rhs) => rhs,
//         })
//     }

//     fn difference<'a>(&'a mut self, rhs: &'a Seq<T>) -> impl Iterator<Item = &'a T> + 'a {
//         let members = Difference {
//             a: self.0.iter().peekable(),
//             b: rhs.0.iter().peekable(),
//         };
//         members.filter_map(|member| match member {
//             Member::Lhs(lhs) => Some(lhs),
//             _ => None,
//         })
//     }

//     fn symmetric_difference<'a>(&'a self, rhs: &'a Seq<T>) -> impl Iterator<Item = &'a T> + 'a {
//         let members = SymmetricDifference {
//             a: self.0.iter().peekable(),
//             b: rhs.0.iter().peekable(),
//         };
//         members.filter_map(|member| match member {
//             Member::Lhs(m) | Member::Rhs(m) => Some(m),
//             _ => None,
//         })
//     }
// }

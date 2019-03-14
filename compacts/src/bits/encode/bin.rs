use crate::{bits::ucast as cast, bits::*};

use super::{Bin, Encode, Map, BLOCK_SIZE, OUT_OF_BOUNDS};

use std::cmp;

impl Default for Bin {
    fn default() -> Self {
        Self::new()
    }
}

impl AsRef<[u16]> for Bin {
    fn as_ref(&self) -> &[u16] {
        &self.0[..]
    }
}
impl AsMut<[u16]> for Bin {
    fn as_mut(&mut self) -> &mut [u16] {
        &mut self.0[..]
    }
}

impl std::ops::Index<usize> for Bin {
    type Output = u16;
    fn index(&self, i: usize) -> &Self::Output {
        &self.0[i]
    }
}

impl std::ops::IndexMut<usize> for Bin {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl<'a> IntoIterator for &'a Bin {
    type Item = &'a u16;
    type IntoIter = std::slice::Iter<'a, u16>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}
impl<'a> IntoIterator for &'a mut Bin {
    type Item = &'a mut u16;
    type IntoIter = std::slice::IterMut<'a, u16>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl IntoIterator for Bin {
    type Item = u16;
    type IntoIter = std::vec::IntoIter<u16>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Bin {
    pub fn new() -> Self {
        Bin(Vec::new())
    }

    pub fn with_capacity(cap: usize) -> Self {
        let vec = Vec::with_capacity(std::cmp::min(cap, Encode::BINARY_HEAP_MAX));
        Bin(vec)
    }

    // assume runs are sorted and have no duplicates.
    pub fn from_runs(iter: impl Iterator<Item = std::ops::RangeInclusive<u16>>) -> Self {
        Bin(iter.flat_map(|r| r).collect::<Vec<u16>>())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    pub fn truncate(&mut self, n: usize) {
        self.0.truncate(n)
    }

    #[inline]
    pub fn search(&self, bit: u16) -> Result<usize, usize> {
        self.0.binary_search(&bit)
    }

    pub fn runs<'a>(&'a self) -> impl Iterator<Item = std::ops::RangeInclusive<u16>> + 'a {
        Runs {
            iter: self.0.iter().peekable(),
        }
    }
}

struct Runs<'a> {
    iter: std::iter::Peekable<std::slice::Iter<'a, u16>>,
}

impl Iterator for Runs<'_> {
    type Item = std::ops::RangeInclusive<u16>;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().and_then(|&n| {
            let mut m = n;
            while let Some(&peek) = self.iter.peek() {
                if m + 1 == *peek {
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

impl FiniteBits for Bin {
    const BITS: u64 = BLOCK_SIZE as u64;
    fn empty() -> Self {
        Self::default()
    }
}

impl Count for Bin {
    fn bits(&self) -> u64 {
        Self::BITS
    }
    fn count1(&self) -> u64 {
        self.0.len() as u64
    }
}

impl Access for Bin {
    fn access(&self, i: u64) -> bool {
        self.search(cast(i)).is_ok()
    }
}

impl Assign<u64> for Bin {
    type Output = ();

    fn set1(&mut self, i: u64) -> Self::Output {
        assert!(i < Self::BITS);
        let i = cast(i);
        if let Err(loc) = self.search(i) {
            self.0.insert(loc, i);
        }
    }
    fn set0(&mut self, i: u64) -> Self::Output {
        assert!(i < Self::BITS);
        let i = cast(i);
        if let Ok(loc) = self.search(i) {
            self.0.remove(loc);
        }
    }
}

// FIXME: This can be more efficient.
impl Assign<std::ops::Range<u64>> for Bin {
    type Output = ();
    fn set1(&mut self, index: std::ops::Range<u64>) -> Self::Output {
        for i in index {
            self.set1(i);
        }
    }
    fn set0(&mut self, index: std::ops::Range<u64>) -> Self::Output {
        for i in index {
            self.set0(i);
        }
    }
}

impl Rank for Bin {
    fn rank1(&self, i: u64) -> u64 {
        assert!(i <= Self::BITS, OUT_OF_BOUNDS);
        let i = i as u16;
        // Search the smallest index `k` that satisfy `vec[k] >= i`,
        // `k` also implies the number of enabled bits in [0, k) (rank1).
        //
        // For example, searching 5 in `[0, 1, 7]` return 2.
        search_index(self.0.len(), |p| {
            self.0.get(p as usize).map_or(false, |&v| v >= i)
        }) as u64
    }
}

impl Select1 for Bin {
    fn select1(&self, c: u64) -> Option<u64> {
        self.0.get(cast::<u64, usize>(c)).map(|&x| cast(x))
    }
}

impl Select0 for Bin {
    fn select0(&self, c: u64) -> Option<u64> {
        self.search0(c)
    }
}

impl<'a> std::ops::BitAndAssign<&'a Bin> for Bin {
    fn bitand_assign(&mut self, that: &'a Bin) {
        *self = {
            let vec1 = &self.0[..];
            let vec2 = &that.0[..];
            let m = vec1.len();
            let n = vec2.len();

            let mut out = Vec::with_capacity(cmp::min(m, n));
            let mut i = 0;
            let mut j = 0;

            while i < m && j < n {
                match vec1[i].cmp(&vec2[j]) {
                    std::cmp::Ordering::Less => {
                        i += 1;
                    }
                    std::cmp::Ordering::Equal => {
                        out.push(vec1[i]);
                        i += 1;
                        j += 1;
                    }
                    std::cmp::Ordering::Greater => {
                        j += 1;
                    }
                }
            }
            Bin(out)
        };
    }
}

impl<'a> std::ops::BitOrAssign<&'a Bin> for Bin {
    fn bitor_assign(&mut self, that: &'a Bin) {
        for &i in that.0.iter() {
            self.set1(cast::<u16, u64>(i));
        }
    }
}

impl<'a> std::ops::BitXorAssign<&'a Bin> for Bin {
    fn bitxor_assign(&mut self, that: &'a Bin) {
        for &i in that.0.iter() {
            let i = cast(i);
            if self.access(i) {
                self.set0(i);
            } else {
                self.set1(i);
            }
        }
    }
}

impl std::ops::Not for Bin {
    type Output = Map<u64>;
    fn not(self) -> Self::Output {
        let mut out = Map::<u64>::splat(!0);
        for &i in self.0.iter() {
            out.set0(cast::<u16, u64>(i));
        }
        out
    }
}
impl std::ops::Not for &'_ Bin {
    type Output = Map<u64>;
    fn not(self) -> Self::Output {
        let mut out = Map::<u64>::splat(!0);
        for &i in self.0.iter() {
            out.set0(cast::<u16, u64>(i));
        }
        out
    }
}

#[cfg(test)]
#[test]
fn number_of_runs() {
    macro_rules! binheap {
        () => { Bin::new() };
        ( $( $bit:expr ),* ) => {
            {
                let mut bin = Bin::new();
                $( bin.set1( $bit ); )*
                bin
            }
        }
    }

    let bin = binheap!();
    assert_eq!(bin.runs().count(), 0);
    assert_eq!(bin, Bin::from_runs(bin.runs()));

    let bin = binheap!(5);
    assert_eq!(bin.runs().count(), 1);
    assert_eq!(bin, Bin::from_runs(bin.runs()));

    let bin = binheap!(0, 1, 2, 3, 4, 5);
    assert_eq!(bin.runs().count(), 1);
    assert_eq!(bin, Bin::from_runs(bin.runs()));

    let bin = binheap!(0, 1, 2, 4, 5);
    assert_eq!(bin.runs().count(), 2);
    assert_eq!(bin, Bin::from_runs(bin.runs()));

    let bin = binheap!(0, 1, 2, 4, 5, 10, 20);
    assert_eq!(bin.runs().count(), 4);
    assert_eq!(bin, Bin::from_runs(bin.runs()));

    let bin = binheap!(0, 1, 2, 4, 5, 10, 20, 40, 41, 42);
    assert_eq!(bin.runs().count(), 5);
    assert_eq!(bin, Bin::from_runs(bin.runs()));

    let bin = binheap!(0, 1, 2, 4, 5, 10, 20, 40, 41, 42, 12312, 12313, 12314);
    assert_eq!(bin, Bin::from_runs(bin.runs()));
}

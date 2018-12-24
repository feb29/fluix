//! Module `bit` defines various traits and types to interact with a bit container.
//!

// # References
//
// Compact Data Structures: A Practical Approach
// Fast, Small, Simple Rank/Select on Bitmaps
// Space-Efficient, High-Performance Rank & Select Structures on Uncompressed Bit Sequences

pub mod ops;

mod array;
mod block;
mod map;
mod seq;
mod vec;

// mod members;

use std::{borrow::Cow, cmp::Ordering, iter::Peekable, marker::PhantomData};
use Ordering::{Equal as EQ, Greater as GT, Less as LT};

use crate::num::Word;

use {block::Encode, ops::*};

pub use {
    array::Array,
    block::{Block, Slice},
    map::Map,
    seq::Seq,
};

pub trait Bit: crate::private::Sealed {
    /// Max size of the bit container.
    ///
    /// There is no guarantee that the container reaches that size.
    /// It can fail to allocate at any point before.
    const MAX_SIZE: u64;

    /// Max value of bit.
    const MAX: u64 = Self::MAX_SIZE - 1;

    #[doc(hidden)]
    type Key: Word;
}

impl Bit for u32 {
    const MAX_SIZE: u64 = BLOCK_SIZE * (1 << Self::Key::SIZE);
    type Key = u16;
}
impl Bit for u64 {
    const MAX_SIZE: u64 = 1 << 63;
    type Key = u64;
}

#[cfg(target_pointer_width = "32")]
impl Bit for usize {
    const MAX_SIZE: u64 = <u32 as Bit>::MAX_SIZE;
    type Key = <u32 as Bit>::Key;
}

#[cfg(target_pointer_width = "64")]
impl Bit for usize {
    const MAX_SIZE: u64 = <u64 as Bit>::MAX_SIZE;
    type Key = <u64 as Bit>::Key;
}

/// Max size of the bit container.
///
/// There is no guarantee that the number of bits reach that size.
/// It can fail to allocate at any point before that size is reached.
const MAX_SIZE: u64 = <u64 as Bit>::MAX_SIZE;

const BLOCK_SIZE: u64 = 1 << 16;

// Panic message.
pub(crate) static OUT_OF_BOUNDS: &str = "index out of bounds";

pub fn sized<T: Bits>(bit: u64) -> Vec<T> {
    assert!(bit < MAX_SIZE);
    let len = crate::num::cast::<u64, usize>(bit / T::SIZE) + 1;
    vec![T::empty(); len]
}

/// Grows vector in-place. If vec has an enough size, nothing happens.
pub fn grow<T: Bits>(vec: &mut Vec<T>, bit: u64) {
    assert!(bit < MAX_SIZE);
    let len = crate::num::cast::<u64, usize>(bit / T::SIZE) + 1;
    if vec.len() < len {
        vec.resize(len, T::empty());
    }
}

pub(crate) struct IxLen {
    start: u64,
    end: u64,
    size: u64,
}

pub(crate) fn ix_len(start: u64, end: u64, size: u64) -> IxLen {
    assert!(start <= end && size > 0);
    IxLen { start, end, size }
}

impl Iterator for IxLen {
    type Item = (u64, u64); // (index, length)
    fn next(&mut self) -> Option<Self::Item> {
        use std::cmp::min;
        let i = self.start;
        let j = self.end;
        let n = self.size;
        if i < j {
            let k = if i / n == (j - 1) / n {
                j // fit in one step
            } else if i % n > 0 {
                // spans many steps, align `i` to multiple of n.
                // this should happen just a once.
                min(i + n - i % n, j)
            } else {
                // spans many steps and `i` is multiple of n.
                min(i + n, j)
            };
            self.start = k;
            Some((i, k - i))
        } else {
            None
        }
    }
}
impl std::iter::FusedIterator for IxLen {}

mod mask {
    pub trait Op {}

    #[derive(Debug)]
    pub struct And;
    #[derive(Debug)]
    pub struct AndNot;
    #[derive(Debug)]
    pub struct Or;
    #[derive(Debug)]
    pub struct Xor;

    impl Op for And {}
    impl Op for AndNot {}
    impl Op for Or {}
    impl Op for Xor {}
}

/// `Step` is an unit of bitwise operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step<K, V> {
    index: K,
    value: V,
    count: u64, // the number of '1' of 'V'
}

/// Trait for bitwise ops. e.g.) And, Or, AndNot and Xor
pub trait IntoSteps {
    type Index;
    type Value;
    type Steps: Iterator<Item = Step<Self::Index, Self::Value>>;

    fn into_steps(self) -> Self::Steps;

    fn and<R>(self, rhs: R) -> Mask<Self, R, mask::And>
    where
        Self: Sized,
    {
        let lhs = self;
        let _op = PhantomData;
        Mask { lhs, rhs, _op }
    }

    fn and_not<R>(self, rhs: R) -> Mask<Self, R, mask::AndNot>
    where
        Self: Sized,
    {
        let lhs = self;
        let _op = PhantomData;
        Mask { lhs, rhs, _op }
    }

    fn or<R>(self, rhs: R) -> Mask<Self, R, mask::Or>
    where
        Self: Sized,
    {
        let lhs = self;
        let _op = PhantomData;
        Mask { lhs, rhs, _op }
    }

    fn xor<R>(self, rhs: R) -> Mask<Self, R, mask::Xor>
    where
        Self: Sized,
    {
        let lhs = self;
        let _op = PhantomData;
        Mask { lhs, rhs, _op }
    }
}

impl<K, V, I> IntoSteps for Box<I>
where
    I: ?Sized + Iterator<Item = Step<K, V>>,
{
    type Index = K;
    type Value = V;
    type Steps = Self;
    fn into_steps(self) -> Self::Steps {
        self
    }
}

#[derive(Debug)]
pub struct Mask<L, R, O: mask::Op> {
    lhs: L,
    rhs: R,
    _op: PhantomData<O>,
}

pub fn and<L, R>(lhs: L, rhs: R) -> Mask<L, R, mask::And> {
    let _op = PhantomData;
    Mask { lhs, rhs, _op }
}
pub fn and_not<L, R>(lhs: L, rhs: R) -> Mask<L, R, mask::AndNot> {
    let _op = PhantomData;
    Mask { lhs, rhs, _op }
}
pub fn or<L, R>(lhs: L, rhs: R) -> Mask<L, R, mask::Or> {
    let _op = PhantomData;
    Mask { lhs, rhs, _op }
}
pub fn xor<L, R>(lhs: L, rhs: R) -> Mask<L, R, mask::Xor> {
    let _op = PhantomData;
    Mask { lhs, rhs, _op }
}

impl<L, R, O: mask::Op> Mask<L, R, O> {
    pub fn and<Rhs>(self, rhs: Rhs) -> Mask<Self, Rhs, mask::And> {
        and(self, rhs)
    }
    pub fn and_not<Rhs>(self, rhs: Rhs) -> Mask<Self, Rhs, mask::AndNot> {
        and_not(self, rhs)
    }
    pub fn or<Rhs>(self, rhs: Rhs) -> Mask<Self, Rhs, mask::Or> {
        or(self, rhs)
    }
    pub fn xor<Rhs>(self, rhs: Rhs) -> Mask<Self, Rhs, mask::Xor> {
        xor(self, rhs)
    }
}

pub struct Steps<L: Iterator, R: Iterator, K, V, O: mask::Op> {
    lhs: Peekable<L>,
    rhs: Peekable<R>,
    _ty: PhantomData<(K, V)>,
    _op: PhantomData<O>,
}

impl<L, R, K, V, O: mask::Op> std::iter::FusedIterator for Steps<L, R, K, V, O>
where
    L: Iterator,
    R: Iterator,
    Self: Iterator,
{
}

impl<L, R, K, V, O: mask::Op> IntoSteps for Mask<L, R, O>
where
    L: IntoSteps<Index = K, Value = V>,
    R: IntoSteps<Index = K, Value = V>,
    Steps<L::Steps, R::Steps, K, V, O>: Iterator<Item = Step<K, V>>,
{
    type Index = K;
    type Value = V;
    type Steps = Steps<L::Steps, R::Steps, K, V, O>;
    fn into_steps(self) -> Self::Steps {
        let lhs = self.lhs.into_steps().peekable();
        let rhs = self.rhs.into_steps().peekable();
        let _ty = PhantomData;
        let _op = PhantomData;
        Steps { lhs, rhs, _ty, _op }
    }
}

impl<L, R, O: mask::Op> IntoIterator for Mask<L, R, O>
where
    Self: IntoSteps,
{
    type Item = Step<<Self as IntoSteps>::Index, <Self as IntoSteps>::Value>;
    type IntoIter = <Self as IntoSteps>::Steps;
    fn into_iter(self) -> Self::IntoIter {
        self.into_steps()
    }
}

pub type Intersection<L, R, K, V> = Steps<L, R, K, V, mask::And>;
pub type Union<L, R, K, V> = Steps<L, R, K, V, mask::Or>;
pub type Difference<L, R, K, V> = Steps<L, R, K, V, mask::AndNot>;
pub type SymmetricDifference<L, R, K, V> = Steps<L, R, K, V, mask::Xor>;

impl<'a, L, R, K: Word, T: Word> Iterator for Intersection<L, R, K, Cow<'a, [T]>>
where
    L: Iterator<Item = Step<K, Cow<'a, [T]>>>,
    R: Iterator<Item = Step<K, Cow<'a, [T]>>>,
{
    type Item = Step<K, Cow<'a, [T]>>;
    fn next(&mut self) -> Option<Self::Item> {
        let lhs = &mut self.lhs;
        let rhs = &mut self.rhs;
        loop {
            match lhs
                .peek()
                .and_then(|x| rhs.peek().map(|y| x.index.cmp(&y.index)))
            {
                Some(LT) => {
                    lhs.next();
                }
                Some(EQ) => {
                    let mut lhs = lhs.next().expect("peek");
                    let rhs = rhs.next().expect("peek");
                    lhs.count = 0;
                    for (x, y) in lhs.value.to_mut().iter_mut().zip(rhs.value.as_ref()) {
                        *x &= *y;
                        lhs.count += x.count1();
                    }
                    break Some(lhs);
                }
                Some(GT) => {
                    rhs.next();
                }
                None => break None,
            }
        }
    }
}

impl<'a, L, R, K: Word> Iterator for Intersection<L, R, K, Slice<'a>>
where
    L: Iterator<Item = Step<K, Slice<'a>>>,
    R: Iterator<Item = Step<K, Slice<'a>>>,
{
    type Item = Step<K, Slice<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        let lhs = &mut self.lhs;
        let rhs = &mut self.rhs;
        loop {
            match lhs
                .peek()
                .and_then(|x| rhs.peek().map(|y| x.index.cmp(&y.index)))
            {
                Some(LT) => {
                    lhs.next();
                }
                Some(EQ) => {
                    let mut lhs = lhs.next().expect("peek");
                    let rhs = rhs.next().expect("peek");
                    lhs.count = lhs.value.intersection(&rhs.value);
                    break Some(lhs);
                }
                Some(GT) => {
                    rhs.next();
                }
                None => break None,
            }
        }
    }
}

impl<'a, L, R, K: Word, T: Word> Iterator for Union<L, R, K, Cow<'a, [T]>>
where
    L: Iterator<Item = Step<K, Cow<'a, [T]>>>,
    R: Iterator<Item = Step<K, Cow<'a, [T]>>>,
{
    type Item = Step<K, Cow<'a, [T]>>;
    fn next(&mut self) -> Option<Self::Item> {
        let lhs = &mut self.lhs;
        let rhs = &mut self.rhs;
        match (lhs.peek(), rhs.peek()) {
            (Some(l), Some(r)) => match l.index.cmp(&r.index) {
                LT => lhs.next(),
                EQ => {
                    let mut lhs = lhs.next().expect("peek");
                    let rhs = rhs.next().expect("peek");
                    lhs.count = 0;
                    for (x, y) in lhs.value.to_mut().iter_mut().zip(rhs.value.as_ref()) {
                        *x |= *y;
                        lhs.count += x.count1();
                    }
                    Some(lhs)
                }
                GT => rhs.next(),
            },
            (Some(_), None) => lhs.next(),
            (None, Some(_)) => rhs.next(),
            (None, None) => None,
        }
    }
}

impl<'a, L, R, K: Word> Iterator for Union<L, R, K, Slice<'a>>
where
    L: Iterator<Item = Step<K, Slice<'a>>>,
    R: Iterator<Item = Step<K, Slice<'a>>>,
{
    type Item = Step<K, Slice<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        let lhs = &mut self.lhs;
        let rhs = &mut self.rhs;
        match (lhs.peek(), rhs.peek()) {
            (Some(l), Some(r)) => match l.index.cmp(&r.index) {
                LT => lhs.next(),
                EQ => {
                    let mut lhs = lhs.next().expect("peek");
                    let rhs = rhs.next().expect("peek");
                    lhs.count = lhs.value.union(&rhs.value);
                    Some(lhs)
                }
                GT => rhs.next(),
            },
            (Some(_), None) => lhs.next(),
            (None, Some(_)) => rhs.next(),
            (None, None) => None,
        }
    }
}

impl<'a, L, R, K: Word, T: Word> Iterator for Difference<L, R, K, Cow<'a, [T]>>
where
    L: Iterator<Item = Step<K, Cow<'a, [T]>>>,
    R: Iterator<Item = Step<K, Cow<'a, [T]>>>,
{
    type Item = Step<K, Cow<'a, [T]>>;
    fn next(&mut self) -> Option<Self::Item> {
        let lhs = &mut self.lhs;
        let rhs = &mut self.rhs;
        loop {
            match (lhs.peek(), rhs.peek()) {
                (Some(l), Some(r)) => match l.index.cmp(&r.index) {
                    LT => return lhs.next(),
                    EQ => {
                        let mut lhs = lhs.next().expect("peek");
                        let rhs = rhs.next().expect("peek");
                        lhs.count = 0;
                        for (x, y) in lhs.value.to_mut().iter_mut().zip(rhs.value.as_ref()) {
                            *x &= !*y;
                            lhs.count += x.count1();
                        }
                        return Some(lhs);
                    }
                    GT => rhs.next(),
                },
                (Some(_), None) => return lhs.next(),
                (None, Some(_)) => rhs.next(),
                (None, None) => return None,
            };
        }
    }
}

impl<'a, L, R, K: Word> Iterator for Difference<L, R, K, Slice<'a>>
where
    L: Iterator<Item = Step<K, Slice<'a>>>,
    R: Iterator<Item = Step<K, Slice<'a>>>,
{
    type Item = Step<K, Slice<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        let lhs = &mut self.lhs;
        let rhs = &mut self.rhs;
        loop {
            match (lhs.peek(), rhs.peek()) {
                (Some(l), Some(r)) => match l.index.cmp(&r.index) {
                    LT => return lhs.next(),
                    EQ => {
                        let mut lhs = lhs.next().expect("peek");
                        let rhs = rhs.next().expect("peek");
                        lhs.count = lhs.value.difference(&rhs.value);
                        return Some(lhs);
                    }
                    GT => rhs.next(),
                },
                (Some(_), None) => return lhs.next(),
                (None, Some(_)) => rhs.next(),
                (None, None) => return None,
            };
        }
    }
}

impl<'a, L, R, K: Word, T: Word> Iterator for SymmetricDifference<L, R, K, Cow<'a, [T]>>
where
    L: Iterator<Item = Step<K, Cow<'a, [T]>>>,
    R: Iterator<Item = Step<K, Cow<'a, [T]>>>,
{
    type Item = Step<K, Cow<'a, [T]>>;
    fn next(&mut self) -> Option<Self::Item> {
        let lhs = &mut self.lhs;
        let rhs = &mut self.rhs;
        match (lhs.peek(), rhs.peek()) {
            (Some(l), Some(r)) => match l.index.cmp(&r.index) {
                LT => lhs.next(),
                EQ => {
                    let mut lhs = lhs.next().expect("peek");
                    let rhs = rhs.next().expect("peek");
                    lhs.count = 0;
                    for (x, y) in lhs.value.to_mut().iter_mut().zip(rhs.value.as_ref()) {
                        *x ^= *y;
                        lhs.count += x.count1();
                    }
                    Some(lhs)
                }
                GT => rhs.next(),
            },
            (Some(_), None) => lhs.next(),
            (None, Some(_)) => rhs.next(),
            (None, None) => None,
        }
    }
}

impl<'a, L, R, K: Word> Iterator for SymmetricDifference<L, R, K, Slice<'a>>
where
    L: Iterator<Item = Step<K, Slice<'a>>>,
    R: Iterator<Item = Step<K, Slice<'a>>>,
{
    type Item = Step<K, Slice<'a>>;
    fn next(&mut self) -> Option<Self::Item> {
        let lhs = &mut self.lhs;
        let rhs = &mut self.rhs;
        match (lhs.peek(), rhs.peek()) {
            (Some(l), Some(r)) => match l.index.cmp(&r.index) {
                LT => lhs.next(),
                EQ => {
                    let mut lhs = lhs.next().expect("peek");
                    let rhs = rhs.next().expect("peek");
                    lhs.count = lhs.value.symmetric_difference(&rhs.value);
                    Some(lhs)
                }
                GT => rhs.next(),
            },
            (Some(_), None) => lhs.next(),
            (None, Some(_)) => rhs.next(),
            (None, None) => None,
        }
    }
}

pub struct Fold<'a, K, V>(Option<BoxedSteps<'a, K, V>>);

type BoxedSteps<'a, K, V> = Box<dyn Iterator<Item = Step<K, V>> + 'a>;

impl<'a, K: 'a, V> Iterator for Fold<'a, K, V> {
    type Item = Step<K, V>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut().and_then(|it| it.next())
    }
}

impl<'a, K: Word, V: 'a> Fold<'a, K, V> {
    fn fold<A, B, F>(xss: impl IntoIterator<Item = A>, f: F) -> Self
    where
        A: IntoSteps<Index = K, Value = V> + 'a,
        B: IntoSteps<Index = K, Value = V> + 'a,
        F: Fn(BoxedSteps<'a, K, V>, A) -> B,
    {
        let mut xss = xss.into_iter();
        Fold(if let Some(head) = xss.next() {
            let head = Box::new(head.into_steps());
            Some(xss.fold(head, |it, x| Box::new(f(it, x).into_steps())))
        } else {
            None
        })
    }

    pub fn and<U>(xss: impl IntoIterator<Item = U>) -> Self
    where
        U: IntoSteps<Index = K, Value = V> + 'a,
        Mask<BoxedSteps<'a, K, V>, U, mask::And>: IntoSteps<Index = K, Value = V>,
    {
        Self::fold(xss, and)
    }

    pub fn or<U>(xss: impl IntoIterator<Item = U>) -> Self
    where
        U: IntoSteps<Index = K, Value = V> + 'a,
        Mask<BoxedSteps<'a, K, V>, U, mask::Or>: IntoSteps<Index = K, Value = V>,
    {
        Self::fold(xss, or)
    }

    pub fn and_not<U>(xss: impl IntoIterator<Item = U>) -> Self
    where
        U: IntoSteps<Index = K, Value = V> + 'a,
        Mask<BoxedSteps<'a, K, V>, U, mask::AndNot>: IntoSteps<Index = K, Value = V>,
    {
        Self::fold(xss, and_not)
    }

    pub fn xor<U>(xss: impl IntoIterator<Item = U>) -> Self
    where
        U: IntoSteps<Index = K, Value = V> + 'a,
        Mask<BoxedSteps<'a, K, V>, U, mask::Xor>: IntoSteps<Index = K, Value = V>,
    {
        Self::fold(xss, xor)
    }
}

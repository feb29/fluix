use std::{
    borrow::Cow,
    cmp::Ordering,
    iter::Peekable,
    marker::PhantomData,
    ops::{BitAndAssign, BitOrAssign, BitXorAssign},
};

use crate::bits::{self, Array, Page, RoaringBlock, UnsignedInt};

mod merge;
mod pad;
mod tuples;

pub use self::{merge::MergeBy, pad::PadUsingDefault, tuples::Tuples};

pub fn and<L, R>(lhs: L, rhs: R) -> And<L, R> {
    And { lhs, rhs }
}

pub fn or<L, R>(lhs: L, rhs: R) -> Or<L, R> {
    Or { lhs, rhs }
}

pub fn xor<L, R>(lhs: L, rhs: R) -> Xor<L, R> {
    Xor { lhs, rhs }
}

pub fn not<T>(val: T) -> Not<T> {
    Not { val }
}

/// And
#[derive(Clone, PartialEq, Eq)]
pub struct And<L, R> {
    pub(crate) lhs: L,
    pub(crate) rhs: R,
}

/// Or
#[derive(Clone, PartialEq, Eq)]
pub struct Or<L, R> {
    pub(crate) lhs: L,
    pub(crate) rhs: R,
}

/// Xor
#[derive(Clone, PartialEq, Eq)]
pub struct Xor<L, R> {
    pub(crate) lhs: L,
    pub(crate) rhs: R,
}

#[derive(Clone, PartialEq, Eq)]
pub struct Not<T> {
    pub(crate) val: T,
}

pub struct AndIntoIter<L: Iterator, R: Iterator, A> {
    lhs: Peekable<L>,
    rhs: Peekable<R>,
    _ty: PhantomData<A>,
}

pub struct OrIntoIter<L: Iterator, R: Iterator, A> {
    lhs: Peekable<L>,
    rhs: Peekable<R>,
    _ty: PhantomData<A>,
}

pub struct XorIntoIter<L: Iterator, R: Iterator, A> {
    lhs: Peekable<L>,
    rhs: Peekable<R>,
    _ty: PhantomData<A>,
}

pub struct NotIntoIter<I: Iterator, A> {
    pad: PadUsingDefault<I, A>,
}

impl<L, R, T> IntoIterator for And<L, R>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    AndIntoIter<L::IntoIter, R::IntoIter, T>: Iterator<Item = T>,
{
    type Item = T;
    type IntoIter = AndIntoIter<L::IntoIter, R::IntoIter, T>;
    fn into_iter(self) -> Self::IntoIter {
        AndIntoIter {
            lhs: self.lhs.into_iter().peekable(),
            rhs: self.rhs.into_iter().peekable(),
            _ty: PhantomData,
        }
    }
}

impl<L, R, T> IntoIterator for Or<L, R>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    OrIntoIter<L::IntoIter, R::IntoIter, T>: Iterator<Item = T>,
{
    type Item = T;
    type IntoIter = OrIntoIter<L::IntoIter, R::IntoIter, T>;
    fn into_iter(self) -> Self::IntoIter {
        OrIntoIter {
            lhs: self.lhs.into_iter().peekable(),
            rhs: self.rhs.into_iter().peekable(),
            _ty: PhantomData,
        }
    }
}

impl<L, R, T> IntoIterator for Xor<L, R>
where
    L: IntoIterator<Item = T>,
    R: IntoIterator<Item = T>,
    XorIntoIter<L::IntoIter, R::IntoIter, T>: Iterator<Item = T>,
{
    type Item = T;
    type IntoIter = XorIntoIter<L::IntoIter, R::IntoIter, T>;
    fn into_iter(self) -> Self::IntoIter {
        XorIntoIter {
            lhs: self.lhs.into_iter().peekable(),
            rhs: self.rhs.into_iter().peekable(),
            _ty: PhantomData,
        }
    }
}

impl<I, T> IntoIterator for Not<I>
where
    I: IntoIterator<Item = T>,
    NotIntoIter<I::IntoIter, T>: Iterator<Item = T>,
{
    type Item = T;
    type IntoIter = NotIntoIter<I::IntoIter, T>;
    fn into_iter(self) -> Self::IntoIter {
        // FIXME
        let range = 0..(bits::MAX_BITS / bits::SHORT_BIT_MAX);
        NotIntoIter {
            pad: PadUsingDefault::pad_using_default(range, self.val.into_iter()),
        }
    }
}

macro_rules! implBitwiseIterator {
    ($($Type:ty),*) => ($(
        impl<'a, L, R, K: UnsignedInt> Iterator for AndIntoIter<L, R, Page<K, Cow<'a, $Type>>>
        where
            L: Iterator<Item = Page<K, Cow<'a, $Type>>>,
            R: Iterator<Item = Page<K, Cow<'a, $Type>>>,
        {
            type Item = Page<K, Cow<'a, $Type>>;
            fn next(&mut self) -> Option<Self::Item> {
                let lhs = &mut self.lhs;
                let rhs = &mut self.rhs;

                let next = loop {
                    match lhs
                        .peek()
                        .and_then(|x| rhs.peek().map(|y| x.index.cmp(&y.index)))
                    {
                        Some(Ordering::Equal) => {
                            let lhs = lhs.next().unwrap();
                            let rhs = rhs.next().unwrap();
                            break Some((lhs, rhs));
                        }
                        Some(Ordering::Less) => {
                            lhs.next();
                        }
                        Some(Ordering::Greater) => {
                            rhs.next();
                        }
                        None => break None,
                    }
                };

                next.map(|(mut lhs, rhs)| {
                    lhs.value.to_mut().0.bitand_assign(&rhs.value.as_ref().0);
                    lhs
                })
            }
        }

        impl<'a, L, R, K: UnsignedInt> Iterator for OrIntoIter<L, R, Page<K, Cow<'a, $Type>>>
        where
            L: Iterator<Item = Page<K, Cow<'a, $Type>>>,
            R: Iterator<Item = Page<K, Cow<'a, $Type>>>,
        {
            type Item = Page<K, Cow<'a, $Type>>;
            fn next(&mut self) -> Option<Self::Item> {
                let lhs = &mut self.lhs;
                let rhs = &mut self.rhs;

                // match compare_entry(lhs.peek(), rhs.peek(), Ordering::Greater, Ordering::Less) {
                //     Ordering::Less => lhs.next(),
                //     Ordering::Equal => {
                //         let mut lhs = lhs.next().expect("unreachable");
                //         let rhs = rhs.next().expect("unreachable");
                //         lhs.to_mut().value.0.bitor_assign(&rhs.value.0);
                //         Some(lhs)
                //     }
                //     Ordering::Greater => rhs.next(),
                // }

                match (lhs.peek(), rhs.peek()) {
                    (Some(l), Some(r)) => match l.index.cmp(&r.index) {
                        Ordering::Less => lhs.next(),
                        Ordering::Equal => {
                            let mut lhs = lhs.next().expect("unreachable");
                            let rhs = rhs.next().expect("unreachable");
                            lhs.value.to_mut().0.bitor_assign(&rhs.value.as_ref().0);
                            Some(lhs)
                        }
                        Ordering::Greater => rhs.next(),
                    },
                    (Some(_), None) => lhs.next(),
                    (None, Some(_)) => rhs.next(),
                    (None, None) => None,
                }
            }
        }

        impl<'a, L, R, K: UnsignedInt> Iterator for XorIntoIter<L, R, Page<K, Cow<'a, $Type>>>
        where
            L: Iterator<Item = Page<K, Cow<'a, $Type>>>,
            R: Iterator<Item = Page<K, Cow<'a, $Type>>>,
        {
            type Item = Page<K, Cow<'a, $Type>>;
            fn next(&mut self) -> Option<Self::Item> {
                let lhs = &mut self.lhs;
                let rhs = &mut self.rhs;

                // match compare_entry(lhs.peek(), rhs.peek(), Ordering::Greater, Ordering::Less) {
                //     Ordering::Less => lhs.next(),
                //     Ordering::Equal => {
                //         let mut lhs = lhs.next().expect("unreachable");
                //         let rhs = rhs.next().expect("unreachable");
                //         lhs.to_mut().value.0.bitxor_assign(&rhs.value.0);
                //         Some(lhs)
                //     }
                //     Ordering::Greater => rhs.next(),
                // }

                match (lhs.peek(), rhs.peek()) {
                    (Some(l), Some(r)) => match l.index.cmp(&r.index) {
                        Ordering::Less => lhs.next(),
                        Ordering::Equal => {
                            let mut lhs = lhs.next().expect("unreachable");
                            let rhs = rhs.next().expect("unreachable");
                            lhs.value.to_mut().0.bitxor_assign(&rhs.value.as_ref().0);
                            Some(lhs)
                        }
                        Ordering::Greater => rhs.next(),
                    },
                    (Some(_), None) => lhs.next(),
                    (None, Some(_)) => rhs.next(),
                    (None, None) => None,
                }
            }
        }

    )*)
}
implBitwiseIterator!(Array, RoaringBlock);

impl<'a, I, K: UnsignedInt> Iterator for NotIntoIter<I, Page<K, Cow<'a, Array>>>
where
    I: Iterator<Item = Page<K, Cow<'a, Array>>>,
{
    type Item = Page<K, Cow<'a, Array>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.pad.next().map(|e| {
            let index = e.index;
            let value = Array(!&e.value.0);
            Page::new(index, Cow::Owned(value))
        })
    }
}

impl<'a, I, K: UnsignedInt> Iterator for NotIntoIter<I, Page<K, Cow<'a, RoaringBlock>>>
where
    I: Iterator<Item = Page<K, Cow<'a, RoaringBlock>>>,
{
    type Item = Page<K, Cow<'a, RoaringBlock>>;
    fn next(&mut self) -> Option<Self::Item> {
        self.pad.next().map(|e| {
            let index = e.index;
            let value = RoaringBlock(!&e.value.0);
            Page::new(index, Cow::Owned(value))
        })
    }
}

pub struct Fold<'a, T>(Option<BoxIter<'a, T>>);

type BoxIter<'a, T> = Box<dyn Iterator<Item = T> + 'a>;

impl<'a, T: 'a> Iterator for Fold<'a, T> {
    type Item = T;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.as_mut().and_then(|it| it.next())
    }
}

impl<'a, T: 'a> Fold<'a, T> {
    /// Combines all given iterators into one iterator by using `And`.
    ///
    /// # Examples
    ///
    /// ```
    /// use compacts::bits::{PageMap, RoaringBlock, Fold, Access};
    /// let bvs = vec![
    ///     PageMap::<u64, RoaringBlock>::from(vec![1, 2, 8, 10]),
    ///     PageMap::<u64, RoaringBlock>::from(vec![2, 6, 8, 10, 12]),
    ///     PageMap::<u64, RoaringBlock>::from(vec![8, 10, 16]),
    /// ];
    /// let out = Fold::and(&bvs).collect::<PageMap<u64, RoaringBlock>>();
    /// assert!(!out.access(2));
    /// assert!( out.access(8));
    /// assert!( out.access(10));
    /// assert!(!out.access(12));
    /// ```
    pub fn and<U>(iters: impl IntoIterator<Item = U>) -> Self
    where
        U: IntoIterator<Item = T> + 'a,
        And<BoxIter<'a, T>, U>: IntoIterator<Item = T>,
    {
        Self::fold(iters, and)
    }

    pub fn or<U>(iters: impl IntoIterator<Item = U>) -> Self
    where
        U: IntoIterator<Item = T> + 'a,
        Or<BoxIter<'a, T>, U>: IntoIterator<Item = T>,
    {
        Self::fold(iters, or)
    }

    pub fn xor<U>(iters: impl IntoIterator<Item = U>) -> Self
    where
        U: IntoIterator<Item = T> + 'a,
        Xor<BoxIter<'a, T>, U>: IntoIterator<Item = T>,
    {
        Self::fold(iters, xor)
    }

    fn fold<A, B>(iters: impl IntoIterator<Item = A>, func: impl Fn(BoxIter<'a, T>, A) -> B) -> Self
    where
        A: IntoIterator<Item = T> + 'a,
        B: IntoIterator<Item = T> + 'a,
    {
        let mut iters = iters.into_iter();
        Fold(if let Some(head) = iters.next() {
            let head = Box::new(head.into_iter());
            Some(iters.fold(head, |it, x| Box::new(func(it, x).into_iter())))
        } else {
            None
        })
    }
}

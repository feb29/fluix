use std::{cmp::Ordering, iter::Peekable};

use Ordering::{Equal as EQ, Greater as GT, Less as LT};

pub struct Intersection<L: Iterator, R: Iterator> {
    pub(crate) a: Peekable<L>,
    pub(crate) b: Peekable<R>,
}

pub struct Union<L: Iterator, R: Iterator> {
    pub(crate) a: Peekable<L>,
    pub(crate) b: Peekable<R>,
}

pub struct Difference<L: Iterator, R: Iterator> {
    pub(crate) a: Peekable<L>,
    pub(crate) b: Peekable<R>,
}

pub struct SymmetricDifference<L: Iterator, R: Iterator> {
    pub(crate) a: Peekable<L>,
    pub(crate) b: Peekable<R>,
}

pub enum Member<T> {
    #[allow(dead_code)]
    And {
        lhs: T,
        rhs: T,
    },
    Lhs(T),
    Rhs(T),
}

impl<L, R, T: Ord> Iterator for Intersection<L, R>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    // None | Member::And
    type Item = Member<T>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match Ord::cmp(self.a.peek()?, self.b.peek()?) {
                LT => {
                    self.a.next();
                }
                EQ => {
                    return Some(Member::And {
                        lhs: self.a.next().unwrap(),
                        rhs: self.b.next().unwrap(),
                    });
                }
                GT => {
                    self.b.next();
                }
            }
        }
    }
}

fn cmp_opt<T: Ord>(x: Option<&T>, y: Option<&T>, short: Ordering, long: Ordering) -> Ordering {
    match (x, y) {
        (None, _) => short,
        (_, None) => long,
        (Some(x1), Some(y1)) => x1.cmp(y1),
    }
}

impl<L, R, T: Ord> Iterator for Union<L, R>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    type Item = Member<T>;
    fn next(&mut self) -> Option<Self::Item> {
        match cmp_opt(self.a.peek(), self.b.peek(), GT, LT) {
            LT => self.a.next().map(|l| Member::Lhs(l)),
            EQ => {
                let lhs = self.b.next().unwrap();
                let rhs = self.a.next().unwrap();
                Some(Member::And { lhs, rhs })
            }
            GT => self.b.next().map(|r| Member::Rhs(r)),
        }
    }
}

impl<L, R, T: Ord> Iterator for Difference<L, R>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    type Item = Member<T>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), LT, LT) {
                LT => return self.a.next().map(|l| Member::Lhs(l)),
                EQ => {
                    let lhs = self.a.next().unwrap();
                    let rhs = self.b.next().unwrap();
                    return Some(Member::And { lhs, rhs });
                }
                GT => {
                    self.b.next();
                }
            }
        }
    }
}

impl<L, R, T: Ord> Iterator for SymmetricDifference<L, R>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    type Item = Member<T>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), GT, LT) {
                LT => return self.a.next().map(|l| Member::Lhs(l)),
                EQ => {
                    let lhs = self.a.next().unwrap();
                    let rhs = self.b.next().unwrap();
                    return Some(Member::And { lhs, rhs });
                }
                GT => return self.b.next().map(|r| Member::Rhs(r)),
            }
        }
    }
}

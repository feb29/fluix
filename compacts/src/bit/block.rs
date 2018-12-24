mod boxed_slice;

use std::{borrow::Cow, cmp::Ordering};
use Ordering::{Equal as EQ, Greater as GT, Less as LT};

use crate::{
    bit::{self, ops::*, Seq},
    num::Word,
};

use boxed_slice::BoxedSlice;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Block(pub(crate) Encode);

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Encode {
    Seq(SeqEncode),
    Vec(VecEncode),
}

type SeqEncode = Seq<u16>;
type VecEncode = BoxedSlice<[u64; Block::VEC_LEN]>;

impl Default for Encode {
    fn default() -> Self {
        Encode::Seq(Seq::new())
    }
}

impl From<SeqEncode> for Encode {
    fn from(data: SeqEncode) -> Self {
        Encode::Seq(data)
    }
}
impl From<VecEncode> for Encode {
    fn from(data: VecEncode) -> Self {
        Encode::Vec(data)
    }
}

/// Clone-on-Write slice.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Slice<'a> {
    Nil,
    Seq(Cow<'a, [u16]>),
    Vec(Cow<'a, [u64]>),
}

impl From<&'_ [u64]> for Block {
    fn from(slice: &'_ [u64]) -> Self {
        let mut vec = Vec::with_capacity(Self::VEC_LEN);
        bit::ix_len(0, bit::BLOCK_SIZE, u64::SIZE)
            .for_each(|(n, len)| vec.push(slice.bits(n, len)));
        Block(Encode::Vec(BoxedSlice::from(vec)))
    }
}
impl From<Cow<'_, [u64]>> for Block {
    fn from(cow: Cow<'_, [u64]>) -> Self {
        Block::from(cow.as_ref())
    }
}

impl From<Slice<'_>> for Block {
    fn from(slice: Slice<'_>) -> Self {
        Block(match slice {
            Slice::Nil => Encode::Seq(SeqEncode::new()),
            Slice::Seq(cow) => {
                if cow.len() >= Self::SEQ_LEN {
                    Encode::Vec({
                        let mut boxed_slice = VecEncode::splat(0);
                        for &b in cow.as_ref() {
                            let i = u64::from(b);
                            boxed_slice.put1(i);
                        }
                        boxed_slice
                    })
                } else {
                    Encode::Seq(Seq(cow.into_owned()))
                }
            }
            Slice::Vec(cow) => Encode::Vec(BoxedSlice::from(cow.into_owned())),
        })
    }
}

impl From<&'_ Seq<u16>> for BoxedSlice<[u64; 1024]> {
    fn from(seq: &SeqEncode) -> Self {
        let mut boxed_slice = Self::splat(0);
        for r in seq.runs() {
            let i = u64::from(*r.start());
            let j = u64::from(*r.end());
            boxed_slice.set1(i..=j);
        }
        boxed_slice
    }
}

impl<'a> From<&'a Block> for Slice<'a> {
    fn from(block: &'a Block) -> Self {
        block.as_slice()
    }
}
impl<'a> From<Option<&'a Block>> for Slice<'a> {
    fn from(block: Option<&'a Block>) -> Self {
        match block {
            Some(b) => Slice::from(b),
            None => Slice::Nil,
        }
    }
}

impl Block {
    pub(crate) const SEQ_LEN: usize = (bit::BLOCK_SIZE / u16::SIZE) as usize;
    pub(crate) const VEC_LEN: usize = (bit::BLOCK_SIZE / u64::SIZE) as usize;

    pub(crate) fn as_slice(&self) -> Slice<'_> {
        match self {
            Block(Encode::Seq(seq)) => Slice::Seq(Cow::Borrowed(&seq[..])),
            Block(Encode::Vec(vec)) => vec.as_cow().map_or(Slice::Nil, Slice::Vec),
        }
    }

    fn fit_to_size(&mut self) {
        if let Block(Encode::Seq(seq)) = self {
            if seq.len() >= Self::SEQ_LEN {
                *self = Block(Encode::Vec(BoxedSlice::from(&*seq)));
            }
        }
    }
}

impl Slice<'_> {
    #[inline]
    fn count(&self) -> u64 {
        match self {
            Slice::Nil => 0,
            Slice::Seq(cow) => cow.len() as u64,
            Slice::Vec(cow) => cow.count1(),
        }
    }

    fn to_boxed_slice(&mut self) {
        if let Slice::Seq(cow) = self {
            let vec = {
                let mut boxed_slice = VecEncode::splat(0);
                for &b in cow.as_ref() {
                    boxed_slice.put1(u64::from(b));
                }
                boxed_slice
            };
            *self = Slice::Vec(Cow::Owned(vec.data.unwrap().to_vec()));
        }
    }
}

macro_rules! delegate {
    ( $this:ident, $method:ident $(, $args:expr )* ) => {
        {
            match $this {
                Block(Encode::Seq(data)) => data.$method( $( $args ),* ),
                Block(Encode::Vec(data)) => data.$method( $( $args ),* ),
            }
        }
    };
}

impl crate::private::Sealed for Block {}

impl Bits for Block {
    const SIZE: u64 = bit::BLOCK_SIZE;
    fn empty() -> Self {
        Self::default()
    }
}

impl BitCount for Block {
    #[inline]
    fn size(&self) -> u64 {
        Self::SIZE
    }
    #[inline]
    fn count1(&self) -> u64 {
        delegate!(self, count1)
    }
}

impl BitGet for Block {
    fn bits<W: Word>(&self, i: u64, n: u64) -> W {
        delegate!(self, bits, i, n)
    }
    fn bit(&self, i: u64) -> bool {
        delegate!(self, bit, i)
    }
    fn ones<'a>(&'a self) -> Box<dyn Iterator<Item = u64> + 'a> {
        delegate!(self, ones)
    }
}

impl BitPut for Block {
    fn put1(&mut self, i: u64) -> u64 {
        let w = delegate!(self, put1, i);
        self.fit_to_size();
        w
    }
    fn put0(&mut self, i: u64) -> u64 {
        delegate!(self, put0, i)
    }
    fn puts<W: Word>(&mut self, i: u64, n: u64, w: W) {
        delegate!(self, puts, i, n, w);
        self.fit_to_size();
    }
}

impl BitRank for Block {
    #[inline]
    fn rank1<Ix: IntoBounds>(&self, i: Ix) -> u64 {
        delegate!(self, rank1, i)
    }
}
impl BitSelect1 for Block {
    #[inline]
    fn select1(&self, n: u64) -> Option<u64> {
        delegate!(self, select1, n)
    }
}
impl BitSelect0 for Block {
    #[inline]
    fn select0(&self, n: u64) -> Option<u64> {
        delegate!(self, select0, n)
    }
}

impl<'a> Slice<'a> {
    pub(crate) fn intersection(&mut self, that: &Slice<'a>) -> u64 {
        match (self, that) {
            (Slice::Seq(seq1), Slice::Seq(seq2)) => {
                let vec1 = seq1.to_mut();
                let vec2 = seq2.as_ref();
                let mut n = 0;
                let mut i = 0;
                let mut j = 0;
                while i < vec1.len() && j < vec2.len() {
                    match vec1[i].cmp(&vec2[j]) {
                        LT => i += 1,
                        EQ => {
                            vec1[n] = vec1[i];
                            n += 1;
                            i += 1;
                            j += 1;
                        }
                        GT => j += 1,
                    }
                }
                vec1.truncate(n);
                vec1.len() as u64
            }

            (Slice::Vec(vec1), Slice::Vec(vec2)) => {
                assert_eq!(vec1.len(), vec2.len());
                let vec1 = vec1.to_mut();
                let vec2 = vec2.as_ref();
                let mut out = 0;
                for (x, y) in vec1.iter_mut().zip(vec2) {
                    *x &= *y;
                    out += x.count1();
                }
                out
            }

            (Slice::Seq(seq), Slice::Vec(vec)) => {
                seq.to_mut().retain(|&x| vec.bit(u64::from(x)));
                // for i in (0..seq.len()).rev() {
                //     if !vec.as_ref().bit(u64::from(seq[i])) {
                //         seq.to_mut().remove(i);
                //     }
                // }
                seq.len() as u64
            }

            (this @ Slice::Vec(_), Slice::Seq(_)) => {
                let mut new_vec = that.clone();
                let count1 = new_vec.intersection(this);
                *this = new_vec;
                count1
            }

            (this @ _, Slice::Nil) => {
                *this = Slice::Nil;
                0
            }

            (Slice::Nil, _) => 0,
        }
    }

    pub(crate) fn union(&mut self, that: &Slice<'a>) -> u64 {
        match (self, that) {
            (Slice::Seq(seq1), Slice::Seq(seq2)) => {
                let vec1 = seq1.to_mut();
                let vec2 = seq2.as_ref();
                let mut i = 0;
                let mut bit = vec2.iter();
                'RHS: for &b2 in &mut bit {
                    while i < vec1.len() {
                        match vec1[i].cmp(&b2) {
                            LT => i += 1,
                            EQ => continue 'RHS,
                            GT => vec1.insert(i, b2),
                        }
                    }
                    vec1.push(b2);
                    break;
                }
                vec1.extend(bit);
                vec1.len() as u64
            }

            (Slice::Vec(vec1), Slice::Vec(vec2)) => {
                assert_eq!(vec1.len(), vec2.len());
                let vec1 = vec1.to_mut();
                let vec2 = vec2.as_ref();
                let mut out = 0;
                for (x, y) in vec1.iter_mut().zip(vec2) {
                    *x |= *y;
                    out += x.count1();
                }
                out
            }

            (Slice::Vec(vec), Slice::Seq(seq)) => {
                for &b in &seq[..] {
                    vec.to_mut().put1(u64::from(b));
                }
                vec.count1()
            }

            (this @ Slice::Seq(_), Slice::Vec(_)) => {
                this.to_boxed_slice();
                this.union(that)
            }

            (this @ Slice::Nil, that @ _) => {
                *this = that.clone();
                this.count()
            }

            (this, Slice::Nil) => this.count(),
        }
    }

    pub(crate) fn difference(&mut self, that: &Slice<'a>) -> u64 {
        match (self, that) {
            (Slice::Seq(seq1), Slice::Seq(seq2)) => {
                let vec1 = seq1.to_mut();
                let vec2 = seq2.as_ref();
                let mut i = 0;
                let mut bit = vec2.iter();
                let mut cur2 = bit.next();
                while i < vec1.len() {
                    match cur2.map(|c2| vec1[i].cmp(c2)) {
                        Some(LT) => {
                            i += 1;
                        }
                        Some(EQ) => {
                            vec1.remove(i);
                            cur2 = bit.next();
                        }
                        Some(GT) => {
                            cur2 = bit.next();
                        }
                        None => break,
                    }
                }
                vec1.len() as u64
            }

            (Slice::Vec(vec1), Slice::Vec(vec2)) => {
                assert_eq!(vec1.len(), vec2.len());
                let vec1 = vec1.to_mut();
                let vec2 = vec2.as_ref();
                let mut out = 0;
                for (x, y) in vec1.iter_mut().zip(vec2) {
                    *x &= !*y;
                    out += x.count1();
                }
                out
            }

            (Slice::Vec(vec), Slice::Seq(seq)) => {
                for &b in &seq[..] {
                    vec.to_mut().put0(u64::from(b));
                }
                vec.count1()
            }

            (Slice::Seq(ref mut seq), Slice::Vec(vec)) => {
                for i in (0..seq.len()).rev() {
                    let b = u64::from(seq[i]);
                    if vec.bit(b) {
                        seq.to_mut().put0(b);
                    }
                }
                seq.len() as u64
            }

            (this, Slice::Nil) => this.count(),
            (this @ Slice::Nil, _) => this.count(),
        }
    }

    pub(crate) fn symmetric_difference(&mut self, that: &Slice<'a>) -> u64 {
        match (self, that) {
            (Slice::Seq(seq1), Slice::Seq(seq2)) => {
                let vec1 = seq1.to_mut();
                let vec2 = seq2.as_ref();
                let mut i = 0;
                let mut bit = vec2.iter();
                let mut cur2 = bit.next();
                while i < vec1.len() {
                    match cur2.map(|c2| vec1[i].cmp(c2)) {
                        Some(LT) => {
                            i += 1;
                        }
                        Some(EQ) => {
                            vec1.remove(i);
                            cur2 = bit.next();
                        }
                        Some(GT) => {
                            vec1.insert(i, *cur2.unwrap());
                            cur2 = bit.next();
                            i += 1;
                        }
                        None => break,
                    }
                }
                if let Some(&cur) = cur2 {
                    vec1.push(cur);
                    vec1.extend(bit);
                }
                vec1.len() as u64
            }

            (Slice::Vec(vec1), Slice::Vec(vec2)) => {
                assert_eq!(vec1.len(), vec2.len());
                let vec1 = vec1.to_mut();
                let vec2 = vec2.as_ref();
                let mut out = 0;
                for (x, y) in vec1.iter_mut().zip(vec2) {
                    *x ^= *y;
                    out += x.count1();
                }
                out
            }

            (Slice::Vec(vec), Slice::Seq(seq)) => {
                for &b in &seq[..] {
                    let b = u64::from(b);
                    if vec.bit(b) {
                        vec.to_mut().put0(b);
                    } else {
                        vec.to_mut().put1(b);
                    }
                }
                vec.count1()
            }

            (this @ Slice::Seq(_), Slice::Vec(_)) => {
                let mut new_vec = that.clone();
                let count1 = new_vec.symmetric_difference(this);
                *this = new_vec;
                count1
            }

            (this @ Slice::Nil, that @ _) => {
                *this = that.clone();
                this.count()
            }

            (this, Slice::Nil) => this.count(),
        }
    }
}

// Reference: https://dl.acm.org/citation.cfm?doid=3077136.3080789

mod dump;

use std::{
    borrow::{Borrow, BorrowMut},
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hash, Hasher},
    marker::PhantomData,
};

use compacts::bits;

type Repr = bits::IndexMap<u64, bits::RoaringBlock>;

// n: 256, fp: 0.06
const DEFAULT_SIZEOF_FILTER: usize = 1500;
const DEFAULT_SIZEOF_HASHES: usize = 5;

/// Signs is an k for filtering data probabilistically.
#[derive(Clone)]
pub struct Signs<S = RandomState> {
    signs: Vec<Repr>, // inverted signatures.
    khash: usize,     // number of hashes for each signatures.
    state: S,         // hash builder.
}

/// Sign is a row of Signs, that represents fingerprint of data (a.k.a bloom filter).
pub struct Sign<B: Borrow<Signs<S>>, S = RandomState> {
    k: u64,
    signs: B,
    state: PhantomData<S>,
}

impl Default for Signs {
    fn default() -> Self {
        new(DEFAULT_SIZEOF_FILTER, DEFAULT_SIZEOF_HASHES)
    }
}

/// m: signature's bit size.
/// k: number of hashes.
pub fn new(m: usize, k: usize) -> Signs {
    Signs::with_hasher(m, k, Default::default())
}

/// n:  number of items you expect to add to the signature.
/// fp: false positive rate.
pub fn optimal(n: usize, fp: f64) -> Signs {
    let (m, k) = optimal_params(n, fp);
    new(m, k)
}

fn optimal_params(n: usize, fp: f64) -> (usize, usize) {
    assert!(n > 0);
    assert!(0.0 < fp && fp < 1.0);

    let m = {
        let t = 2.0f64;
        -((n as f64) * fp.ln() / t.ln().powi(2))
    };

    let k = {
        let t = 2.0f64;
        t.ln() * m / (n as f64)
    };

    (m.ceil() as usize, k.ceil() as usize)
}

impl<S> Signs<S>
where
    S: BuildHasher,
{
    pub fn with_hasher(m: usize, khash: usize, state: S) -> Signs<S> {
        let signs = vec![Repr::default(); m];
        Signs {
            signs,
            khash,
            state,
        }
    }
}

impl<S> Signs<S> {
    pub fn kbits(&self) -> usize {
        self.signs.len()
    }
    pub fn khash(&self) -> usize {
        self.khash
    }

    pub fn bits(&self, i: usize) -> &Repr {
        &self.signs[i]
    }

    pub fn bits_mut(&mut self, i: usize) -> &mut Repr {
        &mut self.signs[i]
    }

    pub fn sign(&self, k: u64) -> Sign<&Signs<S>, S> {
        let signs = self;
        let state = PhantomData;
        Sign { k, signs, state }
    }

    pub fn sign_mut(&mut self, k: u64) -> Sign<&mut Signs<S>, S> {
        let signs = self;
        let state = PhantomData;
        Sign { k, signs, state }
    }
}

fn make_hashes<S, H>(state: &S, t: &H) -> [u64; 4]
where
    H: Hash + ?Sized,
    S: BuildHasher,
{
    let hasher = &mut state.build_hasher();
    let mut hashes = [0; 4];
    for h in &mut hashes {
        t.hash(hasher);
        *h = hasher.finish();
    }
    hashes
}

fn hash_at(h: [u64; 4], i: usize) -> usize {
    let p = h[i % 2].wrapping_add((i as u64).wrapping_mul(h[2 + (((i + (i % 2)) % 4) / 2)]));
    p as usize
}

impl<B, S> Sign<B, S>
where
    B: Borrow<Signs<S>>,
    S: BuildHasher,
{
    pub fn test<H>(&self, h: &H) -> bool
    where
        H: Hash + ?Sized,
    {
        let hashes = make_hashes(&self.signs.borrow().state, h);
        self.test_hashes(hashes)
    }

    fn test_hashes(&self, hs: [u64; 4]) -> bool {
        let signs = self.signs.borrow();
        let kbits = signs.kbits();
        let khash = signs.khash();
        let hashi = |i| hash_at(hs, i) % kbits;
        (0..khash).all(|k| signs.bits(hashi(k)).get(self.k))
    }
}

impl<B, S> Sign<B, S>
where
    B: BorrowMut<Signs<S>>,
    S: BuildHasher,
{
    pub fn add<H>(&mut self, h: &H)
    where
        H: Hash + ?Sized,
    {
        let hashes = make_hashes(&self.signs.borrow().state, h);
        self.add_hashes(hashes)
    }

    fn add_hashes(&mut self, hs: [u64; 4]) {
        let signs = self.signs.borrow_mut();
        let kbits = signs.kbits();
        let khash = signs.khash();
        let hashi = |i| hash_at(hs, i) % kbits;
        for k in 0..khash {
            signs.bits_mut(hashi(k)).insert(self.k);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore]
    fn debug_optimal_params() {
        let docheck = |n: usize, fp: f64| {
            let (kbits, khash) = optimal_params(n, fp);
            let bytes_per_point = (kbits as f64 / n as f64) / 8.0;
            println!(
                "n:{} fp:{:.4}, hash:{}, bits:{}, {:.8}",
                n, fp, khash, kbits, bytes_per_point
            );
        };

        let from_fp = |fp: f64| {
            docheck(1 << 5, fp);
            docheck(1 << 6, fp);
            docheck(1 << 7, fp);
            docheck(1 << 8, fp);
            docheck(1 << 9, fp);
            docheck(1 << 10, fp);
            docheck(1 << 11, fp);
            docheck(1 << 12, fp);
            docheck(1 << 13, fp);

            docheck(1 << 16, fp);
            docheck(1 << 32, fp);
        };

        from_fp(0.01);
        from_fp(0.02);
        from_fp(0.03);
        from_fp(0.04);
        from_fp(0.05);
        from_fp(0.06);
        from_fp(0.10);
        from_fp(0.20);
    }
}

#![feature(test)]

extern crate funnel;

#[macro_use]
extern crate lazy_static;
extern crate rand;
extern crate test;

use rand::{
    distributions::{Alphanumeric, Standard},
    thread_rng, Rng,
};

use test::Bencher;

use funnel::{
    bit,
    signs::{self, Signs},
};

const MAX: u64 = 10_000_000;

lazy_static! {
    static ref SIGNS: Signs = {
        let mut signs = signs::optimal(8, 0.05);

        for i in 0..MAX {
            let log = Log::gen();

            let mut sign = signs.sign_mut(i);
            sign.add(&("uuid", log.uuid));
            sign.add(&("pref", log.pref));
            sign.add(&("unum", log.unum));
            sign.add(&("inum", log.inum));
            for tag in &log.tags {
                sign.add(&("tags", tag));
            }
        }
        signs
    };
}

#[derive(Debug, Clone, Hash)]
struct Log {
    uuid: String,
    pref: usize,
    unum: usize,
    inum: isize,
    tags: Vec<u64>,
}

impl Log {
    fn gen() -> Self {
        let mut rng = thread_rng();

        let uuid = rng.sample_iter(&Alphanumeric).take(10).collect::<String>();
        let pref = rng.gen_range(0, 50);
        let inum = rng.gen_range(0, 1000);
        let unum = rng.gen_range(0, 10000);
        let tags = rng.sample_iter(&Standard).take(4).collect::<Vec<u64>>();

        Log {
            uuid,
            pref,
            unum,
            inum,
            tags,
        }
    }
}

use funnel::bit::ops::*;

macro_rules! fold {
    ($i:expr, $($bvs:expr),*) => {
        $i $( .and($bvs) )*
    };
    ($i:expr, $($bvs:expr),* ,) => {
        $i $( .and($bvs) )*
    };
}

// #[bench]
// fn signatures_filter(bench: &mut Bencher) {
//     let mut accum = 0;
//     let n = 4_000_000;
//     let m = 9_000_000;
//     bench.iter(|| {
//         accum = 0;
//         let selected1 = fold![
//             SIGNS.bits(0).get(n..m),
//             SIGNS.bits(2).get(n..m),
//             SIGNS.bits(3).get(n..m),
//             SIGNS.bits(6).get(n..m),
//             SIGNS.bits(7).get(n..m),
//             SIGNS.bits(8).get(n..m),
//             SIGNS.bits(10).get(n..m),
//             SIGNS.bits(11).get(n..m),
//         ];
//         let selected2 = fold![
//             SIGNS.bits(19).get(n..m),
//             SIGNS.bits(21).get(n..m),
//             SIGNS.bits(26).get(n..m),
//             SIGNS.bits(28).get(n..m),
//             SIGNS.bits(29).get(n..m),
//             SIGNS.bits(31).get(n..m),
//             SIGNS.bits(33).get(n..m),
//             SIGNS.bits(34).get(n..m),
//         ];

//         for page in selected1.and(selected2) {
//             accum += bit::count1(&page.value);
//         }
//     });
// }

#[bench]
fn add(bench: &mut Bencher) {
    let mut signs = Signs::default();
    let mut n = 0;
    bench.iter(|| {
        for i in n..n + 8 {
            signs.sign_mut(0).add(&("data", i));
        }
        n += 8;
    });
}

#[bench]
fn test(bench: &mut Bencher) {
    bench.iter(|| SIGNS.sign(0).test(&("score", 0)));
}

#[bench]
#[ignore]
fn test_all(bench: &mut Bencher) {
    bench.iter(|| {
        let mut r = false;
        for i in 0..MAX {
            let a = SIGNS.sign(i).test(&("data", 1));
            let b = SIGNS.sign(i).test(&("data", 2));
            r = a && b;
        }
        r
    })
}

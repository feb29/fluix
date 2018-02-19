#![feature(test)]

extern crate compacts;
extern crate test;
#[macro_use]
extern crate lazy_static;
extern crate rand;

#[macro_use]
mod gen_bench;

const NBITS: u64 = 150_000;
const BOUND: u64 = 10_000_000;

mod u16 {
    gen_bench!(BitSet, u16, crate::NBITS, crate::BOUND);
}
mod u32 {
    gen_bench!(BitSet, u32, crate::NBITS, crate::BOUND);
}
mod u64 {
    gen_bench!(BitSet, u64, crate::NBITS, crate::BOUND);
}
mod u128 {
    gen_bench!(BitSet, u128, crate::NBITS, crate::BOUND);
}
mod usize {
    gen_bench!(BitSet, usize, crate::NBITS, crate::BOUND);
}

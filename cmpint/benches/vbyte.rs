#![feature(test)]

extern crate bitpacking;
extern crate cmpint;
extern crate rand;
extern crate test;

use bitpacking::{BitPacker, BitPacker1x, BitPacker4x, BitPacker8x};
use cmpint::{varint, vbyte};
use rand::Rng;
use test::Bencher;

const VBYTE: usize = 256;

#[bench]
fn varint_encode(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let mut data: Vec<u32> = vec![];
    for _ in 0..VBYTE {
        data.push(rng.gen());
    }
    let mut buf = vec![0u8; VBYTE * varint::MAX_VARINT_LEN32];

    b.iter(|| {
        let mut n = 0;
        for d in &data {
            n += varint::encode(&mut buf, d);
        }
    })
}

#[bench]
fn vbyte_encode(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let mut data: Vec<u32> = vec![];
    for _ in 0..VBYTE {
        data.push(rng.gen());
    }
    let mut buf = vec![0u8; VBYTE * varint::MAX_VARINT_LEN32];
    let mut ctl = vec![0u8; (data.len() + 3) / 4];

    b.iter(|| {
        let mut n = 0;
        n += vbyte::encode(&mut buf, &mut ctl, &data);
    })
}

#[bench]
fn bitpacking1x_encode(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let mut data = vec![];
    for _ in 0..BitPacker1x::BLOCK_LEN {
        data.push(rng.gen());
    }

    let bitpacker = BitPacker1x::new();
    let num_bits: u8 = bitpacker.num_bits(&data);
    let mut buf = vec![0u8; 4 * BitPacker1x::BLOCK_LEN];
    b.iter(|| {
        let n = bitpacker.compress(&data, &mut buf[..], num_bits);
        assert_eq!((num_bits as usize) * BitPacker1x::BLOCK_LEN / 8, n);
    })
}

#[bench]
fn bitpacking4x_encode(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let mut data = vec![];
    for _ in 0..BitPacker4x::BLOCK_LEN {
        data.push(rng.gen());
    }

    // Detects if `SSE3` is available on the current computed
    // and uses the best available implementation accordingly.
    let bitpacker = BitPacker4x::new();

    // Computes the number of bits used for each integers in the blocks.
    // my_data is assumed to have a len of 128 for `BitPacker4x`.
    let num_bits: u8 = bitpacker.num_bits(&data);

    let mut buf = vec![0u8; 4 * BitPacker4x::BLOCK_LEN];

    b.iter(|| {
        let n = bitpacker.compress(&data, &mut buf[..], num_bits);
        assert_eq!((num_bits as usize) * BitPacker4x::BLOCK_LEN / 8, n);
    })

    // let mut decmp = vec![0u32; BitPacker4x::BLOCK_LEN];
    // bitpacker.decompress(&buf[..n], &mut decmp[..], num_bits);
    // assert_eq!(&data, &decmp);
}

#[bench]
fn bitpacking8x_encode(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let mut data = vec![];
    for _ in 0..BitPacker8x::BLOCK_LEN {
        data.push(rng.gen());
    }

    let bitpacker = BitPacker8x::new();
    let num_bits: u8 = bitpacker.num_bits(&data);
    let mut buf = vec![0u8; 4 * BitPacker8x::BLOCK_LEN];
    b.iter(|| {
        let n = bitpacker.compress(&data, &mut buf[..], num_bits);
        assert_eq!((num_bits as usize) * BitPacker8x::BLOCK_LEN / 8, n);
    })
}

use std::fmt;
use compacts::bits;

const DEFAULT_SIZEOF_FILTER: usize = 256;
const DEFAULT_SIZEOF_HASHES: usize = 4;
const DEFAULT_FP_RATES: f64 = 0.03;

/// Funnel is a simple implementation of `BitFunnel`.
#[derive(Clone)]
pub struct Funnel {
    data: Box<[bits::Set]>,
}

impl Default for Funnel {
    fn default() -> Self {
        let data = {
            let vec = vec![bits::Set::new(); DEFAULT_SIZEOF_FILTER];
            vec.into_boxed_slice()
        };
        Funnel { data }
    }
}

// n is a number of items.
// p is a false positive rate.
fn optimal(n: usize, p: f64) -> (usize, usize) {
    assert!(n > 0);
    assert!(0.0 < p && p < 1.0);

    let size_of_filter = {
        let t = 2.0f64;
        -((n as f64) * p.ln() / t.ln().powi(2))
    };

    let size_of_hashes = {
        let t = 2.0f64;
        t.ln() * size_of_filter / (n as f64)
    };

    (
        size_of_filter.ceil() as usize,
        size_of_hashes.ceil() as usize,
    )
}

impl fmt::Debug for Funnel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for d in self.data.iter() {
            if d.get(0) {
                write!(f, "1")?;
            } else {
                write!(f, "0")?;
            }
        }
        f.pad("\n")
    }
}

// impl Funnel {
//     fn new(size: usize) -> Self {
//         let data = {
//             let vec = vec![bits::Set::new(); size];
//             vec.into_boxed_slice()
//         };
//         Funnel { data }
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn test_debug() {
    //     let funnel = Funnel::default();
    //     println!("{:?}", funnel);

    //     let ix0 = &funnel.data[0];
    //     let ix1 = &funnel.data[1];

    //     println!("{:?}", ix0.and(ix1).collect::<bits::Set>());
    // }

    #[test]
    fn test_optimal() {
        for i in 1..21 {
            let fp = i as f64 / 100.0f64;
            println!("n:  128 fp: {:.2}, {:?}", fp, optimal(128, fp));
            println!("n:  256 fp: {:.2}, {:?}", fp, optimal(256, fp));
            println!("n:  512 fp: {:.2}, {:?}", fp, optimal(512, fp));
            println!("n: 1024 fp: {:.2}, {:?}", fp, optimal(1024, fp));
            println!("n: 2048 fp: {:.2}, {:?}", fp, optimal(2048, fp));
            println!("n: 4096 fp: {:.2}, {:?}", fp, optimal(4096, fp));
        }
    }
}

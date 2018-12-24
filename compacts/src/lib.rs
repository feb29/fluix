// #![deny(warnings)]

mod private {
    pub trait Sealed {}

    macro_rules! impl_Sealed {
        ( $( $Type:ty ),* ) => {
            $( impl Sealed for $Type {} )*
        }
    }
    impl_Sealed!(u8, u16, u32, u64, u128, usize);
}

pub mod bit;
mod num;

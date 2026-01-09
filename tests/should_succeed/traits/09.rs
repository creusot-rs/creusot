extern crate creusot_std;

pub trait Tr {
    type X;
}

pub fn test<T: Tr<X = u32>>(t: T::X) -> u32 {
    t + 0
}

pub fn test2<T: Tr, U: Tr<X = T::X>>(t: T::X) -> U::X {
    t
}

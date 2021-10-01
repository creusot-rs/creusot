trait Tr {
    type X;
}

fn test<T: Tr<X = u32>>(t: T::X) -> u32 {
    t + 0
}

fn test2<T: Tr, U: Tr<X = T::X>>(t: T::X) -> U::X {
    t
}

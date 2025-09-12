extern crate creusot_contracts;
use creusot_contracts::{std::mem::size_of_logic, *};

pub fn f() {
    proof_assert!(size_of_logic::<bool>() == 1);
    proof_assert!(size_of_logic::<char>() == 4);
    proof_assert!(size_of_logic::<u8>() == 1);
    proof_assert!(size_of_logic::<u64>() == 8);
    proof_assert!(size_of_logic::<()>() == 0);
    proof_assert!(size_of_logic::<[u32; 5]>() == 20);
    proof_assert!(size_of_logic::<[(); 5]>() == 0);
}

pub fn g<T>() {
    let t2 = size_of::<[T; 2]>();
    proof_assert!(t2@ == 2 * size_of_logic::<T>());
    proof_assert!(size_of_logic::<&T>() == size_of_logic::<usize>());
    proof_assert!(size_of_logic::<*const T>() == size_of_logic::<usize>());
    proof_assert!(size_of_logic::<Box<T>>() == size_of_logic::<usize>());
    proof_assert!(size_of_logic::<Option<&T>>() == size_of_logic::<usize>());
    proof_assert!(size_of_logic::<Option<Box<T>>>() == size_of_logic::<usize>());
    proof_assert!(size_of_logic::<[T; 5]>() == 5 * size_of_logic::<T>());
    proof_assert!(size_of_logic::<[T; 0]>() == 0);
}

extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub fn test_mut_ref() {
    let mut a = [1, 2].iter();
    assert_eq!((&mut a).next(), Some(&1));
    assert_eq!((&mut a).next(), Some(&2));
    assert_eq!((&mut a).next(), None);
}

pub fn test_filter() {
    let mut a = [true, false, true].iter().filter(
        #[ensures(result == **b)]
        |b: &&bool| **b,
    );
    assert_eq!((&mut a).next(), Some(&true));
    assert_eq!((&mut a).next(), Some(&true));
    assert_eq!((&mut a).next(), None);
}

pub fn test_filter_map() {
    let mut a = [true, false, true].iter().filter_map(
        #[ensures(result == if *b { Some(false) } else { None })]
        |b: &bool| if *b { Some(false) } else { None },
    );
    assert_eq!((&mut a).next(), Some(false));
    assert_eq!((&mut a).next(), Some(false));
    assert_eq!((&mut a).next(), None);
}

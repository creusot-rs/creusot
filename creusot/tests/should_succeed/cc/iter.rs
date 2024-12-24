extern crate creusot_contracts;

pub fn test_mut_ref() {
    let mut a = [1, 2].iter();
    assert_eq!((&mut a).next(), Some(&1));
    assert_eq!((&mut a).next(), Some(&2));
    assert_eq!((&mut a).next(), None);
}

pub fn test_filter_map() {
    let a = [true, false, true].iter().filter_map(|b| if *b { Some(false) } else { None } ).collect::<Vec<_>>();
    assert_eq!(a, [false, false]);
}

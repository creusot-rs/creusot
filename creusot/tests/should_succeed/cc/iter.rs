extern crate creusot_contracts;

pub fn test_mut_ref() {
    let mut a = [1, 2].iter();
    assert_eq!((&mut a).next(), Some(&1));
    assert_eq!((&mut a).next(), Some(&2));
    assert_eq!((&mut a).next(), None);
}

extern crate creusot_contracts;

pub fn test_array() {
    let mut a = [1, 2].iter();
    assert_eq!(a.next(), Some(&1));
    assert_eq!(a.next(), Some(&2));
    assert_eq!(a.next(), None);

    let mut b = ::std::iter::IntoIterator::into_iter([1]);
    assert_eq!(b.next(), Some(1));
    assert_eq!(b.next(), None);
}

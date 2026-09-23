extern crate creusot_std;

pub struct ArrayVec<T: Copy> {
    data: T,
}

impl<T: Copy> ArrayVec<T> {
    fn deref(&self) -> &T {
        panic!()
    }
}

impl<T: Copy + PartialEq> PartialEq<ArrayVec<T>> for ArrayVec<T> {
    fn eq(&self, other: &ArrayVec<T>) -> bool {
        false
    }
}

impl<T: Copy + PartialOrd> PartialOrd<ArrayVec<T>> for ArrayVec<T> {
    fn partial_cmp(&self, other: &ArrayVec<T>) -> Option<core::cmp::Ordering> {
        self.deref().partial_cmp(other.deref())
    }
}

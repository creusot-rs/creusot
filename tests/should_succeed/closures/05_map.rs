// NO_REPLAY

extern crate creusot_std;

pub trait FakeIterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;
}

#[allow(dead_code)]
pub struct Map<I, F> {
    iter: I,
    func: F,
}

impl<A, B, F: Fn(A) -> B, I: FakeIterator<Item = A>> FakeIterator for Map<I, F> {
    type Item = B;

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            None => None,
            Some(e) => Some((self.func)(e)),
        }
    }
}

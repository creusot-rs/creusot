extern crate creusot_contracts;

pub struct S();

impl Iterator for S {
    type Item = ();
    fn next(&mut self) -> Option<()> {
        None
    }
}

extern crate creusot_contracts;

#[derive(Debug)]
pub enum T {
    A { x: i8, y: i8 },
    B(i8, i8, i8, i8, i8, i8),
}

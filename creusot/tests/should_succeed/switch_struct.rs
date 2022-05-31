extern crate creusot_contracts;

pub enum M<T> {
    F { field1: u32 },
    G { field2: T },
}

pub fn test(o: M<u32>) -> bool {
    use M::*;
    match o {
        F { field1 } => field1 > 0,
        G { field2 } => field2 == 0,
    }
}

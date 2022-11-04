extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('x) -> 'x)]
pub fn test<'a: 'b, 'b, X>(x: Result<&'a mut X, &'b mut X>) -> &'b mut X {
    match x {
        Ok(ok) => ok,
        Err(err) => err
    }
}
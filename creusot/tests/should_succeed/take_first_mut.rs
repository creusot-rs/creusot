extern crate creusot_contracts;

use creusot_contracts::*;
use std::mem;

#[ensures(match result {
    Some(r) => {
        *r == (**self_)[0] && ^r == (^*self_)[0] &&
        (**self_)@.len() > 0 && (^*self_)@.len() > 0 &&
        (*^self_)@ == (**self_)@.tail() && (^^self_)@ == (^*self_)@.tail()
    }
    None => (*^self_)@ == Seq::EMPTY && (^*self_)@ == Seq::EMPTY && (**self_)@ == Seq::EMPTY && (^^self_)@ == Seq::EMPTY
})]
pub fn take_first_mut<'a, T>(self_: &mut &'a mut [T]) -> Option<&'a mut T> {
    match mem::take(self_).split_first_mut() {
        None => return None,
        Some((first, rem)) => {
            *self_ = rem;
            Some(first)
        }
    }
}

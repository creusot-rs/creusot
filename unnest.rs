extern crate creusot_contracts;
use creusot_contracts::*;

// #[ensures(match result {
//     Some((first, tail)) => {
//         first == &mut self_[0]
//     }
//     None => true
// })]
// fn split_first_mut<T>(self_: &mut [T]) -> Option<(&mut T, &mut [T])> { todo!() }

#[logic]
fn f<T>(self_: &mut &mut [T], result_: Option<(&mut T, &mut [T])>) -> bool {
    match result_ {
    Some((first, tail)) => {
        first == &mut self_[0]
    }
    None => true
}
}

#[creusot::decl::logic]
fn f2<T>(self_: &mut &mut [T], result_: Option<(&mut T, &mut [T])>) -> bool {
    match result_ {
    Some((first, tail)) => {
        creusot_contracts::__stubs::equal(first, &mut self_[0])
    }
    None => true
}
}
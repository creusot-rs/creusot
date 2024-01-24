extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result == x.0.1)]
pub fn g<'a>(x: ((i32, &'a mut i32), i32)) -> &'a mut i32 {
    &mut *(x.0).1
}

#[ensures(*result == *(*b).1)]
#[ensures(^result == *(^b).1)]
#[ensures(^(*b).1 == ^(^b).1)]
pub fn f1<'a>(b: &'a mut (i32, &'a mut i32)) -> &'a mut i32 {
    &mut *b.1
}

#[ensures(*result == *(*x0).1)]
#[ensures(^result == *(^x0).1)]
#[ensures(^(*x0).1 == ^(^x0).1)]
pub fn f2<'a>(x0: &'a mut (i32, &'a mut i32)) -> &'a mut i32 {
    &mut *x0.1
}

#[ensures(*result == *(*x1).1)]
#[ensures(^result == *(^x1).1)]
#[ensures(^(*x1).1 == ^(^x1).1)]
pub fn f3<'a>(x1: &'a mut (i32, &'a mut i32)) -> &'a mut i32 {
    &mut *x1.1
}

#[ensures(*result == *(*x2).1)]
#[ensures(^result == *(^x2).1)]
#[ensures(^(*x2).1 == ^(^x2).1)]
pub fn f4<'a>(x2: &'a mut (i32, &'a mut i32)) -> &'a mut i32 {
    &mut *x2.1
}

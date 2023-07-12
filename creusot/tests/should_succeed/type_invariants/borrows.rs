extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct NonZero(i32);

impl Invariant for NonZero {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ != 0 }
    }
}

impl NonZero {
    #[requires(n@ != 0)]
    #[ensures(result.0 == n)]
    pub fn new(n: i32) -> Self {
        Self(n)
    }

    #[ensures((*self).0@ == (*result)@)]
    #[ensures((^self).0@ == (^result)@)]
    pub fn inner_mut(&mut self) -> &mut i32 {
        &mut self.0
        // cannot proof (^self).inv() as *self = ^result which is unknown
    }
}

#[requires(x.0@ < i32::MAX@)]
#[requires(x.0@ != -1)]
pub fn simple(x: &mut NonZero) {
    inc(&mut x.0);
    // resolve x, assert x.inv()
}

#[requires(x.0@ < i32::MAX@)]
#[requires(x.0@ != -1)]
pub fn hard(x: &mut NonZero) {
    inc(x.inner_mut());
    // resolve x, assert x.inv()
}

#[requires(x.1.0@ < i32::MAX@)]
#[requires(x.1.0@ != -1)]
pub fn tuple(mut x: (NonZero, &mut NonZero)) {
    x.0 .0 = 0;
    inc(&mut x.1 .0);
    // here we resolve x and thus assert x.inv() which is not provable
}

#[requires(x.1.0@ < i32::MAX@)]
#[requires(x.1.0@ != -1)]
pub fn partial_move(x: (NonZero, &mut NonZero)) {
    let mut a = x.0;
    inc(&mut x.1 .0);
    a.0 = 0;
}

#[requires(x.1.0@ < i32::MAX@)]
#[requires(x.1.0@ != -1)]
pub fn destruct(x: (NonZero, &mut NonZero)) {
    let (mut a, b) = x;
    a.0 = 0;
    inc(&mut b.0);
}

#[requires(x.0@ < i32::MAX@)]
#[requires(x.0@ != -1)]
pub fn frozen_dead<'a>(mut x: &'a mut NonZero, y: &'a mut NonZero) {
    let a = &mut x.0;
    // here we have to resolve x
    // assert x.inv() fails: depends on ^a which is unknown
    #[allow(unused_assignments)]
    x = y;
    inc(a); // assert old(x).inv()
}

pub struct SumTo10 {
    a: i32,
    b: i32,
}

impl Invariant for SumTo10 {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

impl SumTo10 {
    #[requires(self.a@ < i32::MAX@)]
    pub fn foo(&mut self) {
        inc(&mut self.a);
        dec(&mut self.b);
    }
}

#[requires(x@ < i32::MAX@)]
#[ensures((^x)@ == x@ + 1)]
pub fn inc(x: &mut i32) {
    *x += 1;
}

#[requires(x@ > i32::MIN@)]
#[ensures((^x)@ == x@ - 1)]
pub fn dec(x: &mut i32) {
    *x -= 1;
}

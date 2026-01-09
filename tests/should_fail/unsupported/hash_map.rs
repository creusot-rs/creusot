// WHY3PROVE
extern crate creusot_std;
use ::std::collections::HashMap;
use creusot_std::prelude::*;

pub struct Foo(HashMap<u64, u8>);

impl View for Foo {
    type ViewTy = <HashMap<u64, u8> as View>::ViewTy; //FMap<Int, u8>;

    #[logic(open(crate), inline)]
    fn view(self) -> Self::ViewTy {
        self.0.view()
    }
}

impl Foo {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    #[ensures((^self)@.get(num@) == Some(bar))]
    pub fn add(&mut self, num: u64, bar: u8) {
        *self.0.entry(num).or_insert(bar) = bar;
    }
}

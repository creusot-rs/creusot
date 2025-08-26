extern crate creusot_contracts;

use creusot_contracts::{logic::Mapping, *};

#[trusted]
pub struct PredCell<T>(std::cell::Cell<T>);

impl<T> View for PredCell<T> {
    type ViewTy = Mapping<T, bool>;

    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T: Copy> PredCell<T> {
    #[trusted]
    #[ensures(self@[result])]
    pub fn get(&self) -> T {
        self.0.get()
    }

    #[trusted]
    #[requires(self@[v])]
    pub fn set(&self, v: T) {
        self.0.set(v)
    }
}

#[requires(c@ == |z: u32| z.view() % 2 == 0)]
pub fn adds_two(c: &PredCell<u32>) {
    let v = c.get();

    // To shut up overflow checking
    if v < 100000 {
        c.set(v + 2);
    } else {
        c.set(0);
    }
}

extern crate creusot_contracts;

pub trait Ix {
    type Tgt;
    fn ix(&self) -> Self::Tgt;
}

impl Ix for i32 {
    type Tgt = ();

    fn ix(&self) -> <i32 as Ix>::Tgt {
        ()
    }
}

pub fn test<G: Ix<Tgt = u64>, T: Ix<Tgt = u32>>(_a: &T::Tgt, _b: &G::Tgt) -> bool {
    true
}

pub fn test2(a: &i32) {
    a.ix()
}

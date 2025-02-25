extern crate creusot_contracts;

pub trait Ix {
    type Tgt;

    fn ix(&self, ix: usize) -> Self::Tgt;
}

pub fn test<T: Ix>(a: &T) -> T::Tgt
where
    T::Tgt: Eq,
{
    a.ix(0)
}

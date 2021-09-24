trait Ix {
	type Tgt;
	fn ix(&self) -> Self::Tgt;
}

impl Ix for i32 {
	type Tgt = ();

	fn ix(&self) -> <i32 as Ix>::Tgt {
		()
	}
}

fn test<G : Ix<Tgt = u64>, T : Ix<Tgt = u32>>(a : &T::Tgt, b: &G::Tgt) -> bool
{ true
}

fn test2(a: &i32) {
	a.ix()
}
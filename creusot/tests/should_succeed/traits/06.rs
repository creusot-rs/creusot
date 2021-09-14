// WHY3SKIP
trait Ix {
	type Tgt;

	fn ix(&self, ix: usize) -> Self::Tgt;
}

fn test< T : Ix>(a : &T) -> T::Tgt
where T::Tgt : Eq {
	a.ix(0)
}
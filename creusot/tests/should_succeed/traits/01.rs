// WHY3SKIP
trait A {
	fn from_b<B>(x: Self) -> B;
}


fn uses_generic<T : A>(b: T) -> u32 {
	A::from_b(b)
}

fn main() {}

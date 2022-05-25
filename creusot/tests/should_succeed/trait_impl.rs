// This file tests that the implementation of a trait is correctly translated

// #[derive(PartialEq)]
// pub enum Three {
//   I,
//   II,
//   III,
// }

fn main() {}

// trait MyTrait<U> {
//   fn some<T>(self, t: T);
// }

// impl<U> MyTrait<U> for Three {
//   fn some<T>(self, t: T) {}
// }

trait T<B> {
    fn x(self);
}

impl<B, T2, T1: T<B>> T<B> for (T1, T2) {
    fn x(self) {}
}

impl<B> T<B> for u32 {
    fn x(self) {}
}

// trait PartialEq<R> {
//   fn eq(self, rhs: R) -> bool;
// }

// impl PartialEq<()> for u32 {
//   fn eq(self : Self, rhs: ()) -> bool {
//     true
//   }
// }

// module X
//   type t1
//   type t2
//   val x
// end

// scope ImplT1
//   type t1
//   type t2
//   clone T as T1 with type self = t1
//   clone T as T2 with type self = t2

//   clone X with type t1 = t1, type t2 = t2
//   clone T with type self = (t1, t2)

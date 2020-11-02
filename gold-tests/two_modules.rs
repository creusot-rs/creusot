mod mod1 {
	pub enum T { A, B, C }
}

mod mod2 {
  use mod1;

  pub fn x (t : mod1::T) -> bool {
    true
  }
}

use mod1::T::*;

fn main() {
  mod2::x(B);
}

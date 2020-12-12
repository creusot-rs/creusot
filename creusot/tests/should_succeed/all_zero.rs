enum List {
  Cons { value: u32, next : Box<List> },
  Nil,
}
fn all_zero(mut l : &mut List) {
  use List::*;

	while let Cons { value, next} = l {
    *value = 0;
    l = next;
  }
}

fn main () {}

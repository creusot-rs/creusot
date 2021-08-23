// fn uses_two_types<T : PartialOrd, U : PartialOrd>(x: T, y: U) -> bool {
// 	x < x && y < y
// }

fn uses_concrete_instance(x : (u32, u32), y : (u32, u32) ) -> bool {
	x < y
}

// fn uses_super_type<T : Ord>(x: T, y: T) -> bool {
//   // x < y && x == x
//   false
// }


fn main () {}

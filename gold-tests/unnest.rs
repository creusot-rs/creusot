fn main () {
}

fn unnest<'a, 'b : 'a>(x : &'a mut &'b mut u32) -> &'a mut u32 {
  * x
}

struct MyInt(usize);

// Is it possible to construct this argument?
// If each time a borrow is created we require borrowed place to outlive the borrow...
// Why not error though?
// fn unnest2<'b, 'a, MyInt >(x : &'a &'b MyInt) -> &'a MyInt {
//   &** x
// }

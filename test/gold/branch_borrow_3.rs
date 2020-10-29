// fn main () {
//   let mut a = 10;
//   let mut b = 10;
//   let mut c = 10;

//   let mut x = &mut a;
//   let mut y = &mut b;
//   let mut z = &mut c;
//   let mut w;

//   if true {
//     y = x;
//   } else {
//     z = x;
//   }

//   // if true {
//   //   * x = 6;
//   //   z = x;

//   // } else {
//   //   * y = 7;
//   //   z = y;
//   // }
//   w = y;
//   * w = 5;

//   // assume { * z = ^z};
//   // assume { ? = ?};
//   // assume { ? = ?};

//   // assert(a == 5 || b == 5 || c == 5);
// }

struct MyInt(usize);

fn main () {
  let mut a = (MyInt(10), MyInt(5));
  let b = &mut a;

  let c = &mut b.1;
  let d = &mut b.0;

  (* c).0 != (*d).0;
}

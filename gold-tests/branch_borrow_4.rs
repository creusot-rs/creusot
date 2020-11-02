fn main () {
  let mut a = 10;
  let mut b = 10;

  let mut x = &mut a;
  let mut y = &mut b;
  let mut z;
  if true {
    *x = 5;
    w = x;
  } else {
    *y = 6;
    w = y;
    // *x = 5;
    // z = y;
  }

  * w;
  // assume { * z = ^z};
  // assume { ? = ?};
  // assume { ? = ?};

  // assert(a == 5 || b == 5 || c == 5);
}


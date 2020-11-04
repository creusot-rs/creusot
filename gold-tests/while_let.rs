fn main () {
  let mut a = Some(10);

  let b = &mut a;

  // * b = 5;


  while let Some(_) = b {
  	*b = None;
  }

  // a == 15;
}

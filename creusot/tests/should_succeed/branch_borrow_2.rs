fn main () {
  let mut a = 10;
  let mut b = 10;
  let mut c = 10;

  let x = &mut a;
  let y = &mut b;
  let z = &mut c;
  let mut w;


  match 3 {
    1 => { * x = 6; w = x; }
    2 => { * y = 7; w = y; }
    _ => { * z = 8; w = z; }
  }


  * w = 5;

  assert!(c == 5);
}

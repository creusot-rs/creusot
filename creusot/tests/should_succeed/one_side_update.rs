struct MyInt(usize);

fn main () {
	let mut a = MyInt(10);
	let b = &mut a;
	if true {
		a.0 == 10;
	} else {
		*b = MyInt(5);
	}
}

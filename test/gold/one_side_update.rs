fn main () {
	let mut a = 10;
	let b = &mut a;
	if true {
		a == 10;
	} else {
		*b = 5;
	}
}

fn kill(_ : &mut u32) {}
fn test () {
	let mut a = 10;
	kill(&mut a);
}

fn main () {}

struct Something {
	a: u32, b: Option<Box<Something>>
}

fn test (mut a: Something, b: Something) {
  a = b;

}

fn main () {}

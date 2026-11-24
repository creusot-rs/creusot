extern crate creusot_std;
use creusot_std::ghost::invariant::Tokens;

pub fn main() {
    call_twice(Tokens::new);
}

fn call_twice<R>(f: impl Fn() -> R) {
    f();
    f();
}

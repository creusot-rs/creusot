struct T(Box<U>);
struct U(Box<T>);

fn main () {}

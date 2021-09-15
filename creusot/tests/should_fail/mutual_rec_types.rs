struct T(Box<U>);
struct U(Box<T>);

fn test(t: T) {}

fn main() {}

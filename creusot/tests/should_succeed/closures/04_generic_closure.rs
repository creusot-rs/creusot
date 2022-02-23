fn generic_closure<A, B, F: Fn(A) -> B>(f: F, a: A) -> B {
    f(a)
}

fn mapper<A>(x: A) {
    generic_closure(|a| (), x)
}

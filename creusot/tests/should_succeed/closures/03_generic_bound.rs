fn closure_param<F: Fn(u32)>(f: F) {
    (f)(0)
}

fn caller() {
    closure_param(|x: u32| ())
}

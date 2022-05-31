// The output should have `func2` cloning the interface of `func1`
// but `func3` should only clone `func1` as its usage of `func1` is
// internal.

fn func1() {}

fn func2() {
    func1()
}

pub fn func3() {
    func2()
}

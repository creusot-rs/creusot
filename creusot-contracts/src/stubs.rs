#[creusot::spec::no_translate]
#[rustc_diagnostic_item = "fin"]
pub fn fin<T>(_: &mut T) -> T {
    panic!()
}

#[creusot::spec::no_translate]
#[rustc_diagnostic_item = "cur"]
pub fn cur<T>(_: &mut T) -> T {
    panic!()
}

#[creusot::spec::no_translate]
#[rustc_diagnostic_item = "equal"]
pub fn equal<T>(_: T, _: T) -> bool {
    panic!();
}

#[creusot::spec::no_translate]
#[rustc_diagnostic_item = "exists"]
pub fn exists<T, F: Fn(T) -> bool>(_: F) -> bool {
    panic!()
}

#[creusot::spec::no_translate]
#[rustc_diagnostic_item = "forall"]
pub fn forall<T, F: Fn(T) -> bool>(_: F) -> bool {
    panic!()
}

#[creusot::spec::no_translate]
#[rustc_diagnostic_item = "implication"]
pub fn implication(_: bool, _: bool) -> bool {
    panic!();
}

#[creusot::spec::no_translate]
#[rustc_diagnostic_item = "absurd"]
pub fn abs<T>() -> T {
    panic!()
}

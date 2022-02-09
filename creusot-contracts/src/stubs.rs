#[creusot::no_translate]
#[rustc_diagnostic_item = "fin"]
pub fn fin<T>(_: &mut T) -> T {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "cur"]
pub fn cur<T>(_: &mut T) -> T {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "equal"]
pub fn equal<T: ?Sized>(_: T, _: T) -> bool {
    panic!();
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "exists"]
pub fn exists<T, F: Fn(T) -> bool>(_: F) -> bool {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "forall"]
pub fn forall<T, F: Fn(T) -> bool>(_: F) -> bool {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "implication"]
pub fn implication(_: bool, _: bool) -> bool {
    panic!();
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "absurd"]
pub fn abs<T>() -> T {
    panic!()
}

#[creusot::no_translate]
#[rustc_diagnostic_item = "variant_check"]
pub fn variant_check<R: crate::WellFounded>(r: R) -> R {
    r
}

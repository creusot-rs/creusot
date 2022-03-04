#[creusot::no_translate]
#[rustc_diagnostic_item = "fin"]
pub fn fin<T: ?Sized>(_: &mut T) -> Box<T> {
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
#[rustc_diagnostic_item = "old"]
pub fn old<T>(_: T) -> T {
    panic!()
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

// Used to create a constraint forcing the result of an ensures closure to agree with the outside
// #[creusot::no_translate]
// #[rustc_diagnostic_item = "closure_result_constraint"]
// pub fn closure_result<Args, Args2, R, F : FnOnce<Args, Output=R>, G : FnOnce<Args2, Output=R>>(f: F, g: G) { }

#[creusot::no_translate]
#[rustc_diagnostic_item = "closure_result_constraint"]
pub fn closure_result<Args, R, F: FnOnce<Args, Output = R>>(_: F, _: R) {}

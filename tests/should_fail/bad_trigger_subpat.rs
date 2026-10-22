use creusot_std::prelude::*;

#[logic]
pub fn bar<T>(_: T) {}

#[logic]
pub fn foo() {
    forall(
        #[trigger(bar(a))]
        |_x @ (a,): (u32,)| true,
    );
}

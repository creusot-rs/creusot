use creusot_std::prelude::*;

#[logic]
pub fn bar<T>(_: T) {}

#[logic]
pub fn foo() {
    forall(
        #[trigger({
            let _y = 0;
            bar(x)
        })]
        |x: u32| true,
    );
}

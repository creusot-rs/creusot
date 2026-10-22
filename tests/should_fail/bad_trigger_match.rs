use creusot_std::prelude::*;

#[logic]
pub fn bar<T>(_: T) {}

#[logic]
pub fn foo() {
    forall(
        #[trigger({
            match true {
                _ => bar(x),
            }
        })]
        |x: u32| true,
    );
}

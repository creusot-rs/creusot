use crate::*;
pub use ::std::cell::*;

extern_spec! {
    impl<T> UnsafeCell<T> {
        #[check(ghost)]
        fn new(value: T) -> UnsafeCell<T>;
    }

    impl<T: ?Sized> UnsafeCell<T> {
        #[check(ghost)]
        fn get(&self) -> *mut T;
    }
}

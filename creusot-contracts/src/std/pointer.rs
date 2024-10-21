use crate::*;

// We conservatively model raw pointers as having an address *plus some hidden
// metadata*.
//
// This is to account for provenance
// (https://doc.rust-lang.org/std/ptr/index.html#using-strict-provenance) and
// wide pointers. See e.g.
// https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null: "unsized
// types have many possible null pointers, as only the raw data pointer is
// considered, not their length, vtable, etc. Therefore, two pointers that are
// null may still not compare equal to each other."

pub trait PointerExt<T: ?Sized>: Sized {
    #[logic]
    #[ensures(result.addr_logic() == 0)]
    fn null_logic() -> Self;

    #[logic]
    fn addr_logic(self) -> Int;
}

impl<T: ?Sized> PointerExt<T> for *const T {
    #[trusted]
    #[open(self)]
    #[logic]
    #[ensures(result.addr_logic() == 0)]
    fn null_logic() -> Self {
        absurd
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    fn addr_logic(self) -> Int {
        absurd
    }
}

impl<T: ?Sized> PointerExt<T> for *mut T {
    #[trusted]
    #[open(self)]
    #[logic]
    #[ensures(result.addr_logic() == 0)]
    fn null_logic() -> Self {
        absurd
    }

    #[trusted]
    #[predicate]
    #[open(self)]
    fn addr_logic(self) -> Int {
        absurd
    }
}

extern_spec! {
    impl<T> *const T {
        #[ensures(result@ == self.addr_logic())]
        fn addr(self) -> usize;

        #[ensures(result == (self.addr_logic() == 0))]
        fn is_null(self) -> bool;
    }

    impl<T> *mut T {
        #[ensures(result@ == self.addr_logic())]
        fn addr(self) -> usize;

        #[ensures(result == (self.addr_logic() == 0))]
        fn is_null(self) -> bool;
    }

    mod std {
        mod ptr {
            #[ensures(result.addr_logic() == 0)]
            fn null<T>() -> *const T
            where
                T: std::ptr::Thin + ?Sized;

            #[ensures(result.addr_logic() == 0)]
            fn null_mut<T>() -> *mut T
            where
                T: std::ptr::Thin + ?Sized;

            #[ensures(result == (p.addr_logic() == q.addr_logic()))]
            fn addr_eq<T, U>(p: *const T, q: *const U) -> bool
            where
                T: ?Sized, U: ?Sized;
        }
    }
}

use crate::prelude::*;
#[cfg(creusot)]
use crate::std::mem::{align_of_logic, size_of_logic};

use core::alloc::Layout;
#[cfg(creusot)]
use core::{
    alloc::LayoutError,
    mem::{align_of, size_of},
};

pub trait LayoutExt {
    /// Read [`Layout::size`] in logic.
    #[logic]
    fn size_log(self) -> usize;

    /// Read [`Layout::align`] in logic.
    #[logic]
    fn align_log(self) -> usize;
}

impl LayoutExt for Layout {
    #[logic(opaque)]
    fn size_log(self) -> usize {
        dead
    }

    #[logic(opaque)]
    fn align_log(self) -> usize {
        dead
    }
}

/// Returns the rounding up of `n` to the nearest multiple of `of`.
#[logic]
#[requires(n >= 0 && of > 0)]
#[ensures(result >= n)]
#[ensures(exists<m: Int> m * of == result)]
#[ensures(result - of < n)]
pub fn round_nearest_multiple(n: Int, of: Int) -> Int {
    pearlite! {
        let m = crate::logic::such_that(|m: Int| m >= 0 && (m - 1) * of < n && n <= m * of);
        m * of
    }
}

/// Requirements for creating a [`Layout`].
#[logic(open)]
pub fn layout_requirements(size: Int, align: Int) -> bool {
    pearlite! {
        align > 0 &&
        (exists<a: Int> a >= 0 && a.pow2() == align) &&
        align <= isize::MAX@ &&
        round_nearest_multiple(size, align) <= isize::MAX@
    }
}

extern_spec! {
    impl Layout {
        #[ensures(if layout_requirements(size@, align@) {
            exists<res> result == Ok(res) &&
                res.size_log() == size &&
                res.align_log() == align
        } else {
            exists<err> result == Err(err)
        })]
        const fn from_size_align(size: usize, align: usize) -> Result<Layout, LayoutError>;

        #[requires(layout_requirements(size@, align@))]
        #[ensures(result.size_log() == size && result.align_log() == align)]
        const unsafe fn from_size_align_unchecked(size: usize, align: usize) -> Layout;

        #[ensures(result == self.size_log())]
        const fn size(&self) -> usize;

        #[ensures(result == self.align_log())]
        const fn align(&self) -> usize;

        #[requires(layout_requirements(size_of_logic::<T>(), align_of_logic::<T>()@))]
        #[ensures(result.size_log()@ == size_of_logic::<T>())]
        #[ensures(result.align_log() == align_of_logic::<T>())]
        #[ensures(exists<n: Int> result.size_log()@ == n * result.align_log()@)]
        const fn new<T>() -> Layout {
            unsafe { Layout::from_size_align_unchecked(size_of::<T>(), align_of::<T>()) }
        }

        #[ensures(if layout_requirements(self.size_log()@, align@) {
            exists<res> result == Ok(res) &&
                res.size_log() == self.size_log() &&
                res.align_log()@ == self.align_log()@.max(align@)
        } else {
            exists<err> result == Err(err)
        })]
        const fn align_to(&self, align: usize) -> Result<Layout, LayoutError> {
            Layout::from_size_align(self.size(), align)
        }

        #[ensures(if n@ * size_of_logic::<T>() > isize::MAX@ {
            exists<err> result == Err(err)
        } else {
            let s = crate::logic::such_that(|s: usize| s@ == n@ * size_of_logic::<T>());
            if layout_requirements(s@, align_of_logic::<T>()@) {
                exists<res> result == Ok(res) &&
                    res.size_log() == s &&
                    res.align_log() == align_of_logic::<T>()
            } else {
                exists<err> result == Err(err)
            }
        })]
        const fn array<T>(n: usize) -> Result<Layout, LayoutError>;
    }
}

use crate::prelude::*;
#[cfg(all(creusot, feature = "std"))]
use std::alloc::Allocator;

extern_spec! {
    mod core {
        mod convert {
            trait From<T> where Self: From<T> {
                // #[requires(true)]
                fn from(value: T) -> Self;
            }
        }
    }

    impl<T> From<T> for T {
        #[check(ghost)]
        #[ensures(result == self)]
        fn from(self) -> T;
    }

    impl<T, U> Into<U> for T
    where
        U: From<T>,
    {
        // FIXME: inherit terminates/ghost status
        #[requires(<U as From<T>>::from.precondition((self,)))]
        #[ensures(<U as From<T>>::from.postcondition((self,), result))]
        fn into(self) -> U {
            U::from(self)
        }
    }

    impl<T> From<T> for Option<T> {
        #[check(ghost)]
        #[ensures(result == Some(x))]
        fn from(x: T) -> Self;
    }
}

#[cfg(feature = "std")]
extern_spec! {
    impl<T> From<T> for Box<T> {
        #[check(ghost)]
        #[ensures(*result == x)]
        fn from(x: T) -> Self;
    }

    impl<T: Clone> From<&[T]> for Box<[T]>
    {
        // FIXME: inherit ghost/terminates from clone
        #[ensures(result@.len() == s@.len())]
        #[ensures(forall<i> 0 <= i && i < s@.len() ==> <T as Clone>::clone.postcondition((&s@[i],), result@[i]))]
        fn from(s: &[T]) -> Self;
        // To verify: uses CloneToUninit
    }

    impl<T: Clone> From<&mut [T]> for Box<[T]>
    {
        // FIXME: inherit ghost/terminates from clone
        #[ensures(result@.len() == s@.len())]
        #[ensures(forall<i> 0 <= i && i < s@.len() ==> <T as Clone>::clone.postcondition((&s@[i],), result@[i]))]
        #[ensures(^s == *s)]
        fn from(s: &mut [T]) -> Self {
            Box::<[T]>::from(&*s)
        }
    }

    impl<T, const N: usize> From<[T; N]> for Box<[T]> {
        #[check(ghost)]
        #[ensures(result@ == s@)]
        fn from(s: [T; N]) -> Self {
            Box::new(s)
        }
    }

    impl<T: Clone> From<&[T]> for Vec<T>
    {
        // FIXME: inherit ghost/terminates from clone
        #[ensures(result@.len() == s@.len())]
        #[ensures(forall<i> 0 <= i && i < s@.len() ==> <T as Clone>::clone.postcondition((&s@[i],), result@[i]))]
        fn from(s: &[T]) -> Self {
            s.to_vec()
        }
    }

    impl<T: Clone> From<&mut [T]> for Vec<T>
    {
        // FIXME: inherit ghost/terminates from clone
        #[ensures(result@.len() == s@.len())]
        #[ensures(forall<i> 0 <= i && i < s@.len() ==> <T as Clone>::clone.postcondition((&s@[i],), result@[i]))]
        #[ensures(^s == *s)]
        fn from(s: &mut [T]) -> Self {
            s.to_vec()
        }
    }

    impl<T, A: Allocator> From<Box<[T], A>> for Vec<T, A> {
        #[check(ghost)]
        #[ensures(result@ == s@)]
        fn from(s: Box<[T], A>) -> Self {
            s.into_vec()
        }
    }

    impl<T: Clone, const N: usize> From<&[T; N]> for Vec<T> {
        // FIXME: inherit ghost/terminates from clone
        #[ensures(result@.len() == N@)]
        #[ensures(forall<i> 0 <= i && i < s@.len() ==> <T as Clone>::clone.postcondition((&s@[i],), result@[i]))]
        fn from(s: &[T; N]) -> Self {
            Vec::<T>::from(s.as_slice())
        }
    }

    impl<T: Clone, const N: usize> From<&mut [T; N]> for Vec<T> {
        // FIXME: inherit ghost/terminates from clone
        #[ensures(result@.len() == N@)]
        #[ensures(forall<i> 0 <= i && i < s@.len() ==> <T as Clone>::clone.postcondition((&s@[i],), result@[i]))]
        #[ensures(^s == *s)]
        fn from(s: &mut [T; N]) -> Self {
            Vec::<T>::from(s.as_mut_slice())
        }
    }

    impl<T, const N: usize> From<[T; N]> for Vec<T> {
        #[check(ghost)]
        #[ensures(result@ == s@)]
        fn from(s: [T; N]) -> Self {
            <[T]>::into_vec(Box::new(s))
        }
    }

    impl<T, A: Allocator> From<Vec<T, A>> for Box<[T], A> {
        #[check(ghost)]
        #[ensures(result@ == v@)]
        fn from(v: Vec<T, A>) -> Self {
            v.into_boxed_slice()
        }
    }
}

macro_rules! spec_from {
    ($src:ty => $tgt:ty) => {
        extern_spec! {
            impl From<$src> for $tgt {
                #[check(ghost)]
                #[ensures(result == (small as Self))]
                fn from(small: $src) -> Self {
                    small as Self
                }
            }
        }
    };
}

spec_from!(bool => u8);
spec_from!(bool => u16);
spec_from!(bool => u32);
spec_from!(bool => u64);
spec_from!(bool => u128);
spec_from!(bool => usize);
spec_from!(bool => i8);
spec_from!(bool => i16);
spec_from!(bool => i32);
spec_from!(bool => i64);
spec_from!(bool => i128);
spec_from!(bool => isize);

// unsigned -> unsigned
spec_from!(u8 => u16);
spec_from!(u8 => u32);
spec_from!(u8 => u64);
spec_from!(u8 => u128);
spec_from!(u8 => usize);
spec_from!(u16 => u32);
spec_from!(u16 => u64);
spec_from!(u16 => u128);
spec_from!(u16 => usize);
spec_from!(u32 => u64);
spec_from!(u32 => u128);
spec_from!(u64 => u128);

// signed -> signed
spec_from!(i8 => i16);
spec_from!(i8 => i32);
spec_from!(i8 => i64);
spec_from!(i8 => i128);
spec_from!(i8 => isize);
spec_from!(i16 => i32);
spec_from!(i16 => i64);
spec_from!(i16 => i128);
spec_from!(i16 => isize);
spec_from!(i32 => i64);
spec_from!(i32 => i128);
spec_from!(i64 => i128);

// unsigned -> signed
spec_from!(u8 => i16);
spec_from!(u8 => i32);
spec_from!(u8 => i64);
spec_from!(u8 => i128);
spec_from!(u8 => isize);
spec_from!(u16 => i32);
spec_from!(u16 => i64);
spec_from!(u16 => i128);
spec_from!(u32 => i64);
spec_from!(u32 => i128);
spec_from!(u64 => i128);

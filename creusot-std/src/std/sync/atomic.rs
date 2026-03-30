/// Creusot wrapper around [`std::sync::atomic::Ordering`].
#[allow(non_snake_case)]
pub mod Ordering {
    use std::sync::atomic;

    pub trait Ordering {
        const ORDERING: atomic::Ordering;
    }

    pub struct None;

    macro_rules! impl_orders {
        ($( $order:ident ),+) => { $(

            pub struct $order;

            impl Ordering for $order {
                const ORDERING: atomic::Ordering = atomic::Ordering::$order;
            }

        )* };
    }

    impl_orders!(Relaxed, Release, Acquire, SeqCst);
}

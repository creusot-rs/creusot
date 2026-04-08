#[cfg(creusot)]
use crate::mode::Mode;
use crate::{prelude::*, std::iter::Once};

impl<T> View for Once<T> {
    type ViewTy = Option<T>;

    #[logic(opaque)]
    fn view(self) -> Option<T> {
        dead
    }
}

impl<T> IteratorSpec for Once<T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && resolve(self) }
    }

    #[logic(open, prophetic)]
    fn produces(self, _: Mode, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::empty() && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[logic(law)]
    #[ensures(forall<mode: Mode> self.produces(mode, Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(mode, ab, b))]
    #[requires(b.produces(mode, bc, c))]
    #[ensures(a.produces(mode, ab.concat(bc), c))]
    fn produces_trans(
        mode: Mode,
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    ) {
    }
}

extern_spec! {
    impl<T> Iterator for Once<T> {
        #[check(ghost)]
        #[ensures(|result, mode| match result {
            None => self.completed(),
            Some(v) => (*self).produces(mode, Seq::singleton(v), ^self)
        })]
        fn next(&mut self) -> Option<T>;
    }
}

use crate::{
    prelude::*,
    std::iter::{ExactSizeIteratorSpec, Once},
};

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
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::empty() && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

extern_spec! {
    impl<T> Iterator for Once<T> {
        #[check(ghost)]
        #[ensures(match result {
            None => self.completed(),
            Some(v) => (*self).produces(Seq::singleton(v), ^self)
        })]
        fn next(&mut self) -> Option<T>;

        #[check(ghost)]
        #[ensures(result.0 == match self@ { Some(_) => 1usize, None => 0usize })]
        #[ensures(result.1 == Some(result.0))]
        fn size_hint(&self) -> (usize, Option<usize>);
    }
}

impl<T> ExactSizeIteratorSpec for Once<T> {
    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
}

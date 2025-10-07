use crate::{std::iter::Fuse, *};

impl<I: Iterator> View for Fuse<I> {
    type ViewTy = Option<I>;

    #[trusted]
    #[logic(opaque)]
    #[ensures(inv(self) ==> inv(result))]
    #[ensures(forall<other: Fuse<I>> result == other.view() ==> self == other)]
    fn view(self) -> Option<I> {
        dead
    }
}

impl<I: Iterator> Iterator for Fuse<I> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (self@ == None || exists<it:&mut I> it.completed() && self@ == Some(*it)) &&
            (^self)@ == None
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, prod: Seq<Self::Item>, other: Self) -> bool {
        pearlite! {
            match self@ {
                None => prod == Seq::empty() && other@ == self@,
                Some(i) => match other@ {
                    Some(i2) => i.produces(prod, i2),
                    None => false,
                },
            }
        }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

pub trait FusedIterator: ::std::iter::FusedIterator + Iterator {
    #[logic(law)]
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::empty() && ^self == next)]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self);
}

impl<I: Iterator> FusedIterator for Fuse<I> {
    #[logic(open, law)]
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::empty() && ^self == next)]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self) {}
}

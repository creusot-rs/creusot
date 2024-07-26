use crate::{std::iter::Fuse, *};

impl<I: Iterator> ShallowModel for Fuse<I> {
    type ShallowModelTy = Option<I>;

    #[logic]
    #[open(self)]
    #[trusted]
    fn shallow_model(self) -> Option<I> {
        pearlite! { absurd }
    }
}

impl<I: Iterator> Iterator for Fuse<I> {
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (self@ == None || exists<it:&mut I> it.completed() && self@ == Some(*it)) &&
            (^self)@ == None
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, prod: Seq<Self::Item>, other: Self) -> bool {
        pearlite! {
            match self@ {
                None => prod == Seq::EMPTY && other@ == self@,
                Some(i) => match other@ {
                    Some(i2) => i.produces(prod, i2),
                    None => false,
                },
            }
        }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

pub trait FusedIterator: ::std::iter::FusedIterator + Iterator {
    #[law]
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::EMPTY && ^self == next)]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self);
}

impl<I: Iterator> FusedIterator for Fuse<I> {
    #[law]
    #[open]
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::EMPTY && ^self == next)]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self) {}
}

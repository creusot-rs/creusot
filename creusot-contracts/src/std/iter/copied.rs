use crate::{invariant::Invariant, std::iter::Copied, *};

pub trait CopiedExt<I> {
    #[logic]
    fn iter(self) -> I;
}


impl<I> CopiedExt<I> for Copied<I> {
    #[logic]
    #[trusted]
    fn iter(self) -> I {
        pearlite! { absurd }
    }
}


#[trusted]
impl<I> Resolve for Copied<I> {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! {
            self.iter().resolve()
        }
    }
}

impl<I: Invariant> Invariant for Copied<I> {
    #[predicate]
    fn invariant(self) -> bool {
        self.iter().invariant()
    }
}

impl<'a, I, T: 'a> Iterator for Copied<I>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { exists<inner : &mut _> *inner == self.iter() && ^inner == (^self).iter() && inner.completed() }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>> self.iter().produces(s, o.iter())
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> visited[i] == *s[i]
        }
    }

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

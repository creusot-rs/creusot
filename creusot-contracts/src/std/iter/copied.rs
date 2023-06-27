use crate::{invariant::Invariant, std::iter::Copied, *};

pub trait CopiedExt<I> {
    #[logic]
    fn iter(self) -> I;
}

impl<I> CopiedExt<I> for Copied<I> {
    #[open]
    #[logic]
    #[trusted]
    fn iter(self) -> I {
        pearlite! { absurd }
    }
}

#[trusted]
impl<I> Resolve for Copied<I> {
    #[open]
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! {
            self.iter().resolve()
        }
    }
}

impl<I: Iterator> Invariant for Copied<I> {}

impl<'a, I, T: 'a> Iterator for Copied<I>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    #[open]
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { exists<inner : &mut _> *inner == self.iter() && ^inner == (^self).iter() && inner.completed() }
    }

    #[open]
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>> self.iter().produces(s, o.iter())
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> visited[i] == *s[i]
        }
    }

    #[law]
    #[open(self)]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[open(self)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

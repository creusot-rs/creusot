use crate::{invariant::*, std::iter::Copied, *};

pub trait CopiedExt<I> {
    #[logic]
    fn iter(self) -> I;
}

impl<I> CopiedExt<I> for Copied<I> {
    #[open]
    #[logic]
    #[trusted]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        pearlite! { absurd }
    }
}

#[trusted]
impl<I> Resolve for Copied<I> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! {
            resolve(&self.iter())
        }
    }
}

impl<'a, I, T: 'a> Iterator for Copied<I>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<inner : &mut _> inv(inner)
                && *inner == self.iter()
                && ^inner == (^self).iter()
                && inner.completed()
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>> inv(s)
                && self.iter().produces(s, o.iter())
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> visited[i] == *s[i]
        }
    }

    #[law]
    #[open(self)]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

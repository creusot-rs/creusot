use crate::{invariant::Invariant, std::iter::Enumerate, *};

pub trait EnumerateExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> Int;
}

impl<I> EnumerateExt<I> for Enumerate<I> {
    #[trusted]
    #[logic]
    fn iter(self) -> I {
        absurd
    }

    #[trusted]
    #[logic]
    fn n(self) -> Int {
        absurd
    }
}

#[trusted]
impl<I> Resolve for Enumerate<I> {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! {
            self.iter().resolve()
        }
    }
}

impl<I: Invariant + Iterator> Invariant for Enumerate<I> {
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            self.iter().invariant()
            && (forall<s: Seq<I::Item>, i: I> self.iter().produces(s, i) ==> self.n() + s.len() < @std::usize::MAX)
            && (forall<i: &mut I> i.completed() ==> i.produces(Seq::EMPTY, ^i))
        }
    }
}

impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
{
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { exists<inner : &mut _> *inner == self.iter() && ^inner == (^self).iter() && inner.completed() }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == o.n() - self.n()
            && exists<s: Seq<I::Item>> self.iter().produces(s, o.iter())
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> @visited[i].0 == self.n() + i && visited[i].1 == s[i]
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

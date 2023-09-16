use crate::{
    invariant::{inv, Invariant},
    *,
};

pub struct MapInv<I: Invariant, B, F> {
    pub iter: I,
    pub func: F,
    pub produced: Ghost<Seq<B>>,
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Iterator
    for MapInv<I, I::Item, F>
{
    #[open]
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            *(^self).produced == Seq::EMPTY &&
            self.iter.completed() && self.func == (^self).func
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

    #[open]
    #[predicate]
    #[why3::attr = "inline:trivial"]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func.unnest(succ.func)
            && exists<s : Seq<I::Item>> s.len() == visited.len() && self.iter.produces(s, succ.iter)
            && succ.produced.inner() == self.produced.concat(s)
            && exists<fs: Seq<&mut F>> fs.len() == visited.len()
            && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
            && if visited.len() == 0 { self.func == succ.func }
               else { *fs[0] == self.func &&  ^fs[visited.len() - 1] == succ.func }
            && forall<i : Int> 0 <= i && i < visited.len() ==>
                 self.func.unnest(*fs[i])
                 && (*fs[i]).precondition((s[i], Ghost::new(self.produced.concat(s.subsequence(0, i)))))
                 && fs[i].postcondition_mut((s[i], Ghost::new(self.produced.concat(s.subsequence(0, i)))), visited[i])
        }
    }
}

#[trusted]
impl<I: Invariant, B, F> Resolve for MapInv<I, B, F> {
    #[open]
    #[predicate]
    fn resolve(self) -> bool {
        self.iter.resolve() && self.func.resolve()
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> Invariant
    for MapInv<I, I::Item, F>
{
    // Should not quantify over self or the `invariant` cannot be made into a type invariant
    #[open(self)]
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            Self::reinitialize() &&
            self.preservation_inv() &&
            self.next_precondition()
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> ::std::iter::Iterator
    for MapInv<I, I::Item, F>
{
    type Item = B;

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces_one(v, ^self)
    })]
    #[maintains(inv(mut self))]
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => {
                proof_assert! { self.func.precondition((v, self.produced)) };
                #[allow(path_statements)]
                let _: Ghost<()> = gh! { {Self::produces_one_invariant; ()} };
                let produced = gh! { self.produced.push(v) };
                let r = Some((self.func)(v, gh! { self.produced.inner() })); // FIXME: Ghost should be Copy
                self.produced = produced;
                r
            }
            None => {
                self.produced = gh! { Seq::EMPTY };
                None
            }
        }
    }
}

impl<I: Iterator, B, F: FnMut(I::Item, Ghost<Seq<I::Item>>) -> B> MapInv<I, I::Item, F> {
    #[open]
    #[predicate]
    #[creusot::open_inv]
    pub fn next_precondition(self) -> bool {
        pearlite! {
            forall<e: I::Item, i: I>
                self.iter.produces(Seq::singleton(e), i) ==>
                self.func.precondition((e, self.produced))
        }
    }

    #[open]
    #[predicate]
    pub fn reinitialize() -> bool {
        pearlite! {
            forall<reset: &mut MapInv<I, _, F>>
                reset.completed() ==>
                inv((^reset).iter) ==>
                (^reset).next_precondition() &&
                Self::preservation((^reset).iter, (^reset).func)
        }
    }

    #[open(self)]
    #[predicate]
    #[ensures(self.produced.inner() == Seq::EMPTY ==> result == Self::preservation(self.iter, self.func))]
    #[creusot::open_inv]
    pub fn preservation_inv(self) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                self.func.unnest(*f) ==>
                self.iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Ghost::new(self.produced.concat(s)))) ==>
                f.postcondition_mut((e1, Ghost::new(self.produced.concat(s))), b) ==>
                (^f).precondition((e2, Ghost::new(self.produced.concat(s).push(e1))))
        }
    }

    #[open]
    #[predicate]
    pub fn preservation(iter: I, func: F) -> bool {
        pearlite! {
            forall<s: Seq<I::Item>, e1: I::Item, e2: I::Item, f: &mut F, b: B, i: I>
                func.unnest(*f) ==>
                iter.produces(s.push(e1).push(e2), i) ==>
                (*f).precondition((e1, Ghost::new(s))) ==>
                f.postcondition_mut((e1, Ghost::new(s)), b) ==>
                (^f).precondition((e2, Ghost::new(s.push(e1))))
        }
    }

    #[ghost]
    #[open(self)]
    #[requires(self.produces_one(e, other))]
    #[requires(inv(other.iter))]
    #[ensures(inv(other))]
    fn produces_one_invariant(self, e: B, other: Self) {}

    #[open]
    #[predicate]
    #[ensures(result == self.produces(Seq::singleton(visited), succ))]
    pub fn produces_one(self, visited: B, succ: Self) -> bool {
        pearlite! {
            exists<f: &mut F> *f == self.func && ^f == succ.func
            && { exists<e: I::Item> self.iter.produces(Seq::singleton(e), succ.iter)
                 && succ.produced.inner() == self.produced.push(e)
                 && (*f).precondition((e, self.produced))
                 && f.postcondition_mut((e, self.produced), visited) }
        }
    }
}

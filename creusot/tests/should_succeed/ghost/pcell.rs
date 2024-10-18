extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
pub struct Id(());

impl Id {
    /// Generate a fresh id.
    ///
    /// To ensure that it is different from previously generated ids, see [`Self::differentiate`].
    #[trusted]
    #[pure]
    #[requires(true)]
    #[ensures(true)]
    fn fresh() -> Self {
        Self(())
    }

    /// When creating two `PCell`s, we don't know that their ids are different.
    ///
    /// This function allows us to derive exactly that.
    #[trusted]
    #[pure]
    #[ensures(*self == ^self)]
    #[ensures(^self != *other)]
    fn differentiate(&mut self, other: &Self) {}
}

pub struct PCell<T> {
    id: Id,
    inner: std::cell::Cell<T>,
}

pub struct Token<T> {
    id: Id,
    value: T,
}
impl<T> View for Token<T> {
    type ViewTy = Self;
    #[logic]
    #[open]
    fn view(self) -> Self {
        self
    }
}
impl<T> Token<T> {
    #[trusted]
    #[ensures(self.id != other.id)]
    pub fn disjoint(&mut self, other: &Self) {}
}

impl<T> PCell<T> {
    #[trusted]
    #[pure]
    fn conjure_token() -> Token<T> {
        loop {}
    }

    #[trusted]
    #[ensures(result.0.id == result.1@.id)]
    #[ensures(result.1@.value == value)]
    pub fn new(value: T) -> (Self, GhostBox<Token<T>>) {
        let id = Id::fresh();
        let token = ghost! {
            Self::conjure_token()
        };
        let this = Self { id, inner: std::cell::Cell::new(value) };
        (this, token)
    }

    #[trusted]
    #[requires(self.id == token.inner().id)]
    #[ensures(result == token.inner().value)]
    pub fn get(&self, token: GhostBox<&Token<T>>) -> T
    where
        T: Copy,
    {
        self.inner.get()
    }

    #[trusted]
    #[requires(self.id == (*token.inner()).id)]
    #[ensures(self.id == (^token.inner()).id)]
    #[ensures(value == (^token.inner()).value)]
    pub fn set(&self, token: GhostBox<&mut Token<T>>, value: T)
    where
        T: Copy,
    {
        self.inner.set(value);
    }

    #[trusted]
    #[requires(self.id == (*token.inner()).id)]
    #[ensures(self.id == (^token.inner()).id)]
    #[ensures(result == (*token.inner()).value)]
    #[ensures(value == (^token.inner()).value)]
    pub fn replace(&self, token: GhostBox<&mut Token<T>>, value: T) -> T {
        self.inner.replace(value)
    }

    #[trusted]
    #[requires(self.id == (*self_t.inner()).id)]
    #[ensures(self.id == (^self_t.inner()).id)]
    #[requires(other.id == (*other_t.inner()).id)]
    #[ensures(other.id == (^other_t.inner()).id)]
    #[ensures((^self_t.inner()).value == (*other_t.inner()).value)]
    #[ensures((*self_t.inner()).value == (^other_t.inner()).value)]
    pub fn swap(
        &self,
        mut self_t: GhostBox<&mut Token<T>>,
        other: &Self,
        mut other_t: GhostBox<&mut Token<T>>,
    ) {
        ghost! {
            let self_val = &mut self_t.value;
            let other_val = &mut other_t.value;
            std::mem::swap(self_val, other_val);
        };
        self.inner.swap(&other.inner);
    }

    #[trusted]
    #[requires(self.id == token.inner().id)]
    #[ensures(result == token.inner().value)]
    pub fn into_inner(self, token: GhostBox<Token<T>>) -> T {
        self.inner.into_inner()
    }
}

pub fn use_pcell() {
    let (pcell, mut token) = PCell::new(1);
    let value = pcell.get(token.borrow());
    proof_assert!(value@ == 1);

    pcell.set(token.borrow_mut(), 2);

    let value = pcell.get(token.borrow());
    proof_assert!(value@ == 2);

    let old_value = pcell.replace(token.borrow_mut(), 3);
    proof_assert!(old_value@ == 2);

    let value = pcell.get(token.borrow());
    proof_assert!(value@ == 3);

    let (other_pcell, mut other_token) = PCell::new(4);
    {
        let mut token = token.borrow_mut();
        let other_token = other_token.borrow();
        ghost! {
            token.id.differentiate(&other_token.id);
        }
    };
    pcell.swap(token.borrow_mut(), &other_pcell, other_token.borrow_mut());

    proof_assert!(token.inner().id != other_token@.id);

    let value = pcell.into_inner(token);
    proof_assert!(value@ == 4);
}

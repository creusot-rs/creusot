#![feature(min_specialization)]
extern crate creusot_contracts;

use creusot_contracts::*;
use resolve::structural_resolve;

pub enum OwnResult<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> Resolve for OwnResult<T, E> {
    #[open]
    #[logic(prophetic)]
    fn resolve(self) -> bool {
        match self {
            OwnResult::Ok(t) => resolve(&t),
            OwnResult::Err(e) => resolve(&e),
        }
    }

    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<T, E> OwnResult<T, E> {
    #[ensures(result == exists<t: T> *self == OwnResult::Ok(t))]
    pub fn is_ok(&self) -> bool {
        matches!(*self, OwnResult::Ok(_))
    }

    #[ensures(result == exists<e: E> *self == OwnResult::Err(e))]
    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    #[ensures(forall<t: T> self == OwnResult::Ok(t) ==> result == Some(t))]
    #[ensures((exists<e: E> self == OwnResult::Err(e)) ==> result == None)]
    pub fn ok(self) -> Option<T> {
        match self {
            OwnResult::Ok(x) => Some(x),
            #[allow(unused_variables)]
            OwnResult::Err(x) => None,
        }
    }

    #[ensures((exists<t: T> self == OwnResult::Ok(t)) ==> result == None)]
    #[ensures(forall<e: E> self == OwnResult::Err(e) ==> result == Some(e))]
    pub fn err(self) -> Option<E> {
        match self {
            #[allow(unused_variables)]
            OwnResult::Ok(x) => None,
            OwnResult::Err(x) => Some(x),
        }
    }

    #[ensures(forall<t: &T> *self == OwnResult::Ok(*t) ==> result == OwnResult::Ok(t))]
    #[ensures(forall<e: &E> *self == OwnResult::Err(*e) ==> result == OwnResult::Err(e))]
    pub fn as_ref(&self) -> OwnResult<&T, &E> {
        match *self {
            OwnResult::Ok(ref x) => OwnResult::Ok(x),
            OwnResult::Err(ref x) => OwnResult::Err(x),
        }
    }

    #[ensures(
        exists<t: &mut T> *self == OwnResult::Ok(*t) &&
            ^self == OwnResult::Ok(^t) &&
            result == OwnResult::Ok(t) ||
        exists<e: &mut E> *self == OwnResult::Err(*e) &&
            ^self == OwnResult::Err(^e) &&
            result == OwnResult::Err(e)
    )]
    pub fn as_mut(&mut self) -> OwnResult<&mut T, &mut E> {
        match *self {
            OwnResult::Ok(ref mut x) => OwnResult::Ok(x),
            OwnResult::Err(ref mut x) => OwnResult::Err(x),
        }
    }

    #[requires(exists<t: T> self == OwnResult::Ok(t))]
    #[ensures(OwnResult::Ok(result) == self)]
    pub fn unwrap(self) -> T
    where
        E: ::std::fmt::Debug,
    {
        match self {
            OwnResult::Ok(t) => t,
            OwnResult::Err(_e) => panic!(),
        }
    }

    #[requires(exists<t: T> self == OwnResult::Ok(t))]
    #[ensures(OwnResult::Ok(result) == self)]
    pub fn expect(self, msg: &str) -> T
    where
        E: ::std::fmt::Debug,
    {
        match self {
            OwnResult::Ok(t) => t,
            OwnResult::Err(_e) => panic!(),
        }
    }

    #[requires(exists<e: E> self == OwnResult::Err(e))]
    #[ensures(OwnResult::Err(result) == self)]
    pub fn unwrap_err(self) -> E
    where
        T: ::std::fmt::Debug,
    {
        match self {
            OwnResult::Ok(_t) => panic!(),
            OwnResult::Err(e) => e,
        }
    }

    #[ensures(forall<t: T> self == OwnResult::Ok(t) ==> result == t)]
    #[ensures((exists<e: E> self == OwnResult::Err(e)) ==> result == default)]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            OwnResult::Ok(t) => t,
            #[allow(unused_variables)]
            OwnResult::Err(e) => default,
        }
    }

    #[ensures(forall<t: T> self == OwnResult::Ok(t) ==> result == t)]
    #[ensures((exists<e: E> self == OwnResult::Err(e)) ==> T::default.postcondition((), result))]
    pub fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        match self {
            OwnResult::Ok(x) => x,
            OwnResult::Err(_) => T::default(),
        }
    }

    #[ensures((exists<t: T> self == OwnResult::Ok(t)) ==> result == res)]
    #[ensures(forall<e: E> self == OwnResult::Err(e) ==> result == OwnResult::Err(e))]
    pub fn and<U>(self, res: OwnResult<U, E>) -> OwnResult<U, E> {
        match self {
            #[allow(unused_variables)]
            OwnResult::Ok(x) => res,
            OwnResult::Err(e) => OwnResult::Err(e),
        }
    }

    #[ensures(forall<t: T> self == OwnResult::Ok(t) ==> result == OwnResult::Ok(t))]
    #[ensures((exists<e: E> self == OwnResult::Err(e)) ==> result == res)]
    pub fn or<F>(self, res: OwnResult<T, F>) -> OwnResult<T, F> {
        match self {
            OwnResult::Ok(v) => OwnResult::Ok(v),
            #[allow(unused_variables)]
            OwnResult::Err(e) => res,
        }
    }
}

impl<T, E> OwnResult<&T, E> {
    #[ensures(forall<t: &T> self == OwnResult::Ok(t) ==> result == OwnResult::Ok(*t))]
    #[ensures(forall<e: E> self == OwnResult::Err(e) ==> result == OwnResult::Err(e))]
    pub fn copied(self) -> OwnResult<T, E>
    where
        T: Copy,
    {
        //self.map(|&t| t)
        match self {
            OwnResult::Ok(t) => OwnResult::Ok(*t),
            OwnResult::Err(e) => OwnResult::Err(e),
        }
    }

    #[ensures(match (self, result) {
        (OwnResult::Ok(s), OwnResult::Ok(r)) => T::clone.postcondition((s,), r),
        (OwnResult::Err(s), OwnResult::Err(r)) => s == r,
        _ => false
    })]
    pub fn cloned(self) -> OwnResult<T, E>
    where
        T: Clone,
    {
        //self.map(|t| t.clone())
        match self {
            OwnResult::Ok(t) => OwnResult::Ok(t.clone()),
            OwnResult::Err(e) => OwnResult::Err(e),
        }
    }
}

impl<T, E> OwnResult<&mut T, E> {
    #[ensures(forall<t: &mut T> self == OwnResult::Ok(t) ==> result == OwnResult::Ok(*t) && resolve(&t))]
    #[ensures(forall<e: E> self == OwnResult::Err(e) ==> result == OwnResult::Err(e))]
    pub fn copied(self) -> OwnResult<T, E>
    where
        T: Copy,
    {
        //self.map(|&mut t| t)
        match self {
            OwnResult::Ok(t) => OwnResult::Ok(*t),
            OwnResult::Err(e) => OwnResult::Err(e),
        }
    }

    #[ensures(match (self, result) {
        (OwnResult::Ok(s), OwnResult::Ok(r)) => T::clone.postcondition((s,), r),
        (OwnResult::Err(s), OwnResult::Err(r)) => s == r,
        _ => false
    })]
    pub fn cloned(self) -> OwnResult<T, E>
    where
        T: Clone,
    {
        //self.map(|t| t.clone())
        match self {
            OwnResult::Ok(t) => OwnResult::Ok(t.clone()),
            OwnResult::Err(e) => OwnResult::Err(e),
        }
    }
}

impl<T, E> OwnResult<Option<T>, E> {
    #[ensures(self == OwnResult::Ok(None) ==> result == None)]
    #[ensures(forall<t: T> self == OwnResult::Ok(Some(t)) ==> result == Some(OwnResult::Ok(t)))]
    #[ensures(forall<e: E> self == OwnResult::Err(e) ==> result == Some(OwnResult::Err(e)))]
    pub fn transpose(self) -> Option<OwnResult<T, E>> {
        match self {
            OwnResult::Ok(Some(x)) => Some(OwnResult::Ok(x)),
            OwnResult::Ok(None) => None,
            OwnResult::Err(e) => Some(OwnResult::Err(e)),
        }
    }
}

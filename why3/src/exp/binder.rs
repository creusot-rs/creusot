use std::collections::HashMap;

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

use crate::{Ident, ty::Type};

/// An argument to a lambda.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Binder {
    /// `let f _ = ..`
    Wild,
    /// `let f int : bool = ..`
    UnNamed(Type),
    /// `let f a  = ..          `
    Named(Ident),
    /// `let f (ghost? a _ c: int) = ..`
    Typed(bool, Box<[Option<Ident>]>, Type),
}

impl Binder {
    pub fn typed(id: Ident, ty: Type) -> Self {
        Binder::Typed(false, Box::new([Some(id)]), ty)
    }

    pub fn ghost(id: Ident, ty: Type) -> Self {
        Binder::Typed(true, Box::new([Some(id)]), ty)
    }

    /// Return a wildcard binder `_` of type `ty`.
    pub fn wild(ty: Type) -> Self {
        Binder::Typed(false, Box::new([None]), ty)
    }

    pub(crate) fn refresh(&mut self, bound: &mut HashMap<Ident, Ident>) {
        match self {
            Binder::Wild => {}
            Binder::UnNamed(_) => {}
            Binder::Named(id) => {
                let id2 = id.refresh();
                bound.insert(*id, id2);
                *id = id2;
            }
            Binder::Typed(_, ids, _) => {
                for id in ids.iter_mut().flatten() {
                    let id2 = id.refresh();
                    bound.insert(*id, id2);
                    *id = id2;
                }
            }
        }
    }
}

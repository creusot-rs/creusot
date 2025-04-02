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
    /// `let f (ghost? a _ c : int) = ..`
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

    /// Get all the variables defined by this binder.
    pub fn fvs(&self) -> Vec<Ident> {
        match self {
            Binder::Wild => Vec::new(),
            Binder::UnNamed(_) => Vec::new(),
            Binder::Named(id) => vec![id.clone()],
            Binder::Typed(_, ids, _) => ids.iter().flatten().cloned().collect(),
        }
    }

    /// Given that `self`'s type is `ty`, collect all the variables defined by `self` in `out`.
    fn flatten_inner(self, ty: &Type, out: &mut Vec<(Ident, Type)>) {
        match self {
            Binder::Wild => out.push(("_".into(), ty.clone())),
            Binder::UnNamed(ty2) => {
                assert!(ty == &ty2);
                out.push(("_".into(), ty2))
            }
            Binder::Named(id) => out.push((id, ty.clone())),
            Binder::Typed(_, ids, ty2) => {
                assert!(ty == &ty2);
                for i in ids.into_iter().flatten() {
                    out.push((i, ty.clone()));
                }
            }
        }
    }

    /// Collect all the variables defined by `self`, along with their type.
    pub fn var_type_pairs(self) -> Vec<(Ident, Type)> {
        if let Binder::Typed(_, _, ty) = &self {
            let mut out = Vec::new();
            let ty = &ty.clone();
            self.flatten_inner(ty, &mut out);
            out
        } else {
            panic!("cannot get name and type for binder")
        }
    }
}

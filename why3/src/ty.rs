use crate::{Ident, QName};
use indexmap::IndexSet;

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Type {
    Bool,
    Char,
    Integer,
    MutableBorrow(Box<Type>),
    TVar(Ident),
    TConstructor(QName),
    TApp(Box<Type>, Vec<Type>),
    Tuple(Vec<Type>),
    TFun(Box<Type>, Box<Type>),
}

impl Type {
    pub const UNIT: Self = Self::Tuple(Vec::new());

    pub fn predicate(ty: Self) -> Self {
        Self::TFun(Box::new(ty), Box::new(Self::Bool))
    }

    pub fn tapp(mut self, args: Vec<Self>) -> Self {
        if args.is_empty() {
            self
        } else {
            match self {
                Self::TApp(_, ref mut args1) => {
                    args1.extend(args);
                    self
                }
                _ => Self::TApp(Box::new(self), args),
            }
        }
    }

    pub(crate) fn complex(&self) -> bool {
        use Type::*;
        !matches!(self, Bool | Char | Integer | TVar(_) | Tuple(_) | TConstructor(_))
    }

    pub(crate) fn find_used_types(&self, tys: &mut IndexSet<QName>) {
        use Type::*;

        match self {
            MutableBorrow(t) => t.find_used_types(tys),
            TConstructor(qn) => {
                tys.insert(qn.clone());
            }
            TApp(f, args) => {
                f.find_used_types(tys);
                args.iter().for_each(|arg| arg.find_used_types(tys));
            }
            Tuple(args) => {
                args.iter().for_each(|arg| arg.find_used_types(tys));
            }
            TFun(a, b) => {
                a.find_used_types(tys);
                b.find_used_types(tys);
            }
            _ => (),
        }
    }
}

use crate::{Ident, QName};

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Type {
    TVar(Ident),
    TConstructor(QName),
    TApp(Box<Type>, Box<[Type]>),
    Tuple(Box<[Type]>),
    TFun(Box<Type>, Box<Type>),
}

impl Type {
    pub fn unit() -> Self {
        Self::Tuple(Box::new([]))
    }

    pub fn tapp(self, args: impl IntoIterator<Item = Self>) -> Self {
        let args: Box<[_]> = args.into_iter().collect();
        if args.is_empty() { self } else { Self::TApp(Box::new(self), args) }
    }

    pub(crate) fn complex(&self) -> bool {
        use Type::*;
        !matches!(self, TVar(_) | Tuple(_) | TConstructor(_))
    }
}

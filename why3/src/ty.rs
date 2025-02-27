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
        let mut args = args.into_iter().peekable();
        if args.peek().is_none() { self } else { Self::TApp(Box::new(self), args.collect()) }
    }

    pub(crate) fn complex(&self) -> bool {
        use Type::*;
        !matches!(self, TVar(_) | Tuple(_) | TConstructor(_))
    }
}

use crate::{Ident, QName};

#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Type {
    TVar(Ident),
    TConstructor(QName),
    TApp(Box<Type>, Vec<Type>),
    Tuple(Vec<Type>),
    TFun(Box<Type>, Box<Type>),
}

impl Type {
    pub const UNIT: Self = Self::Tuple(Vec::new());

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
        !matches!(self, TVar(_) | Tuple(_) | TConstructor(_))
    }
}

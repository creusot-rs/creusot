use crate::{
    exp::{Exp, Pattern},
    ty::Type,
    Ident, QName,
};
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

pub mod printer;

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Block {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct BlockId(pub usize);

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Terminator {
    Goto(BlockId),
    Absurd,
    Return,
    Switch(Exp, Vec<(Pattern, Terminator)>),
}

impl Terminator {
    pub fn retarget(&mut self, from: BlockId, to: BlockId) {
        match self {
            Self::Goto(id) if *id == from => *id = to,
            Self::Switch(_, brs) => brs.iter_mut().for_each(|(_, t)| t.retarget(from, to)),
            _ => {}
        }
    }

    pub fn is_goto(&self) -> bool {
        matches!(self, Self::Goto(..))
    }
}

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Statement {
    Assign { lhs: Ident, rhs: Exp },
    Invariant(Ident, Exp),
    Variant(Exp),
    Assume(Exp),
    Assert(Exp),
}

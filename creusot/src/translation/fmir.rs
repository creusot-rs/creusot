use crate::{backend::place::projection_ty, pearlite::Term, util::ident_of};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{tcx::PlaceTy, BasicBlock, BinOp, Local, ProjectionElem, Promoted, UnOp},
    ty::{AdtDef, GenericArgsRef, Ty, TyCtxt},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::VariantIdx;

use super::pearlite::Pattern;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place<'tcx> {
    pub(crate) local: Symbol,
    pub(crate) projection: Vec<ProjectionElem<Symbol, Ty<'tcx>>>,
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> Ty<'tcx> {
        let mut ty = PlaceTy::from_ty(locals[&self.local].ty);

        for p in &self.projection {
            ty = projection_ty(ty, tcx, *p);
        }

        ty.ty
    }

    pub(crate) fn as_symbol(&self) -> Option<Symbol> {
        if self.projection.is_empty() {
            Some(self.local)
        } else {
            None
        }
    }
}

#[derive(Clone, Debug)]
pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, RValue<'tcx>, Span),
    Resolve { did: DefId, subst: GenericArgsRef<'tcx>, pl: Place<'tcx>, pat: Option<Pattern<'tcx>> },
    Assertion { cond: Term<'tcx>, msg: String },
    AssumeBorrowInv(Place<'tcx>),
    // Todo: fold into `Assertion`
    AssertTyInv { pl: Place<'tcx>, pat: Option<Pattern<'tcx>> },
    Call(Place<'tcx>, DefId, GenericArgsRef<'tcx>, Vec<Operand<'tcx>>, Span),
}

// TODO: Add shared borrows?
#[derive(Clone, Copy, Debug)]
pub enum BorrowKind {
    /// Ordinary mutable borrows
    Mut,
    /// The source of this borrow is not used after the reborrow, and thus we can
    /// inherit the prophecy identifier.
    ///
    /// The second field is an index in `place.projection`: see
    /// [`NotFinalPlaces::is_final_at`](crate::analysis::NotFinalPlaces::is_final_at).
    Final(usize),
}

#[derive(Clone, Debug)]
pub enum RValue<'tcx> {
    Ghost(Term<'tcx>),
    Borrow(BorrowKind, Place<'tcx>),
    Operand(Operand<'tcx>),
    BinOp(BinOp, Operand<'tcx>, Operand<'tcx>),
    UnaryOp(UnOp, Operand<'tcx>),
    Constructor(DefId, GenericArgsRef<'tcx>, Vec<Operand<'tcx>>),
    Cast(Operand<'tcx>, Ty<'tcx>, Ty<'tcx>),
    Tuple(Vec<Operand<'tcx>>),
    Len(Operand<'tcx>),
    Array(Vec<Operand<'tcx>>),
    Repeat(Operand<'tcx>, Operand<'tcx>),
}

impl<'tcx> RValue<'tcx> {
    /// Returns true if the expression generates verification conditions
    pub fn is_pure(&self) -> bool {
        match &self {
            RValue::Operand(_) => true,
            RValue::BinOp(BinOp::Add | BinOp::Mul | BinOp::Rem | BinOp::Div | BinOp::Sub, _, _) => {
                false
            }
            RValue::BinOp(_, _, _) => true,
            RValue::UnaryOp(UnOp::Neg, _) => false,
            RValue::UnaryOp(_, _) => true,
            RValue::Constructor(_, _, _) => true,
            RValue::Cast(_, _, _) => false,
            RValue::Tuple(_) => true,
            RValue::Len(_) => true,
            RValue::Array(_) => true,
            RValue::Repeat(_, _) => true,
            RValue::Ghost(_) => true,
            RValue::Borrow(_, _) => false,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Operand<'tcx> {
    Move(Place<'tcx>),
    Copy(Place<'tcx>),
    Constant(Term<'tcx>),
    Promoted(Promoted, Ty<'tcx>),
}

impl<'tcx> Operand<'tcx> {
    pub fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> Ty<'tcx> {
        match self {
            Operand::Move(pl) => pl.ty(tcx, locals),
            Operand::Copy(pl) => pl.ty(tcx, locals),
            Operand::Constant(t) => t.ty,
            Operand::Promoted(_, ty) => *ty,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(self::Operand<'tcx>, Branches<'tcx>),
    Return,
    Abort(Span),
}

#[derive(Clone, Debug)]
pub enum Branches<'tcx> {
    Int(Vec<(i128, BasicBlock)>, BasicBlock),
    Uint(Vec<(u128, BasicBlock)>, BasicBlock),
    Constructor(
        AdtDef<'tcx>,
        GenericArgsRef<'tcx>,
        Vec<(VariantIdx, BasicBlock)>,
        Option<BasicBlock>,
    ),
    Bool(BasicBlock, BasicBlock),
}

impl<'tcx> Terminator<'tcx> {
    pub fn targets(&self) -> Box<dyn Iterator<Item = BasicBlock> + '_> {
        use std::iter::*;
        match self {
            Terminator::Goto(bb) => Box::new(once(*bb)),
            Terminator::Switch(_, brs) => match brs {
                Branches::Int(brs, def) => Box::new(brs.iter().map(|(_, b)| *b).chain(once(*def))),
                Branches::Uint(brs, def) => Box::new(brs.iter().map(|(_, b)| *b).chain(once(*def))),
                Branches::Constructor(_, _, brs, def) => {
                    Box::new(brs.iter().map(|(_, b)| *b).chain(*def))
                }
                Branches::Bool(f, t) => Box::new([*f, *t].into_iter()),
            },
            Terminator::Return => Box::new(empty()),
            Terminator::Abort(_) => Box::new(empty()),
        }
    }
}

impl<'tcx> Branches<'tcx> {
    pub fn targets_mut(&mut self) -> Box<dyn Iterator<Item = &mut BasicBlock> + '_> {
        use std::iter::*;
        match self {
            Branches::Int(brs, def) => Box::new(brs.iter_mut().map(|(_, b)| b).chain(once(def))),
            Branches::Uint(brs, def) => Box::new(brs.iter_mut().map(|(_, b)| b).chain(once(def))),
            Branches::Constructor(_, _, brs, def) => {
                Box::new(brs.iter_mut().map(|(_, b)| b).chain(def.as_mut()))
            }
            Branches::Bool(f, t) => Box::new([f, t].into_iter()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Block<'tcx> {
    pub(crate) invariants: Vec<Term<'tcx>>,
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) stmts: Vec<Statement<'tcx>>,
    pub(crate) terminator: Terminator<'tcx>,
}

/// A MIR local along with an optional human-readable name
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum LocalIdent {
    Anon(Local),
    User(Symbol),
}

impl LocalIdent {
    pub(crate) fn anon(loc: Local) -> Self {
        LocalIdent::Anon(loc)
    }

    pub(crate) fn dbg_raw(_: Local, name: Symbol) -> Self {
        LocalIdent::User(name)
    }

    pub(crate) fn symbol(&self) -> Symbol {
        match &self {
            LocalIdent::User(id) => Symbol::intern(&format!("{}", &*ident_of(*id))),
            LocalIdent::Anon(loc) => Symbol::intern(&format!("_{}", loc.index())),
        }
    }
}

pub type LocalDecls<'tcx> = IndexMap<Symbol, LocalDecl<'tcx>>;

#[derive(Clone, Debug)]
pub struct LocalDecl<'tcx> {
    // Original MIR local
    pub(crate) span: Span,
    pub(crate) ty: Ty<'tcx>,
    // Is this a MIR temporary?
    pub(crate) temp: bool,
    // Is this declaration a function argument or return place?
    pub(crate) arg: bool,
}

#[derive(Clone, Debug)]
pub struct Body<'tcx> {
    // TODO: Split into return local, args, and true locals?
    // TODO: Remove usage of `LocalIdent`.
    pub(crate) locals: LocalDecls<'tcx>,
    pub(crate) arg_count: usize,
    pub(crate) blocks: IndexMap<BasicBlock, Block<'tcx>>,
    pub(crate) fresh: usize
}

pub(crate) trait FmirVisitor<'tcx>: Sized {
    fn visit_body(&mut self, body: &Body<'tcx>) {
        super_visit_body(self, body);
    }

    fn visit_block(&mut self, block: &Block<'tcx>) {
        super_visit_block(self, block);
    }

    fn visit_stmt(&mut self, stmt: &Statement<'tcx>) {
        super_visit_stmt(self, stmt);
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>) {
        super_visit_operand(self, operand);
    }

    fn visit_place(&mut self, place: &Place<'tcx>) {
        super_visit_place(self, place);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>) {
        super_visit_terminator(self, terminator);
    }

    fn visit_term(&mut self, _: &Term<'tcx>) {
        ()
    }

    fn visit_rvalue(&mut self, rval: &RValue<'tcx>) {
        super_visit_rvalue(self, rval);
    }
}

pub(crate) fn super_visit_body<'tcx, V: FmirVisitor<'tcx>>(visitor: &mut V, body: &Body<'tcx>) {
    for block in &body.blocks {
        visitor.visit_block(&block.1);
    }
}

pub(crate) fn super_visit_block<'tcx, V: FmirVisitor<'tcx>>(visitor: &mut V, block: &Block<'tcx>) {
    for stmt in &block.stmts {
        visitor.visit_stmt(stmt);
    }

    visitor.visit_terminator(&block.terminator);
}

pub(crate) fn super_visit_stmt<'tcx, V: FmirVisitor<'tcx>>(
    visitor: &mut V,
    stmt: &Statement<'tcx>,
) {
    match stmt {
        Statement::Assignment(place, rval, _) => {
            visitor.visit_place(place);
            visitor.visit_rvalue(rval);
        }
        Statement::Resolve { pl, .. } => {
            visitor.visit_place(pl);
        }
        Statement::Assertion { cond, .. } => {
            visitor.visit_term(cond);
        }
        Statement::AssumeBorrowInv(place) => {
            visitor.visit_place(place);
        }
        Statement::AssertTyInv { pl, .. } => {
            visitor.visit_place(pl);
        }
        Statement::Call(place, _, _, operands, _) => {
            visitor.visit_place(place);
            for operand in operands {
                visitor.visit_operand(operand);
            }
        }
    }
}

pub(crate) fn super_visit_operand<'tcx, V: FmirVisitor<'tcx>>(
    visitor: &mut V,
    operand: &Operand<'tcx>,
) {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            visitor.visit_place(place);
        }
        Operand::Constant(_) => (),
        Operand::Promoted(_, _) => (),
    }
}

pub(crate) fn super_visit_place<'tcx, V: FmirVisitor<'tcx>>(_: &mut V, _: &Place<'tcx>) {
    ()
}

pub(crate) fn super_visit_terminator<'tcx, V: FmirVisitor<'tcx>>(
    visitor: &mut V,
    terminator: &Terminator<'tcx>,
) {
    match terminator {
        Terminator::Goto(_) => (),
        Terminator::Switch(op, _) => {
            visitor.visit_operand(op);
        }
        Terminator::Return => (),
        Terminator::Abort(_) => (),
    }
}

pub(crate) fn super_visit_rvalue<'tcx, V: FmirVisitor<'tcx>>(visitor: &mut V, rval: &RValue<'tcx>) {
    match rval {
        RValue::Ghost(term) => {
            visitor.visit_term(term);
        }
        RValue::Borrow(_, place) => {
            visitor.visit_place(place);
        }
        RValue::Operand(op) => {
            visitor.visit_operand(op);
        }
        RValue::BinOp(_, op1, op2) => {
            visitor.visit_operand(op1);
            visitor.visit_operand(op2);
        }
        RValue::UnaryOp(_, op) => {
            visitor.visit_operand(op);
        }
        RValue::Constructor(_, _, ops) => {
            for op in ops {
                visitor.visit_operand(op);
            }
        }
        RValue::Cast(op, _, _) => {
            visitor.visit_operand(op);
        }
        RValue::Tuple(ops) => {
            for op in ops {
                visitor.visit_operand(op);
            }
        }
        RValue::Len(op) => {
            visitor.visit_operand(op);
        }
        RValue::Array(ops) => {
            for op in ops {
                visitor.visit_operand(op);
            }
        }
        RValue::Repeat(op1, op2) => {
            visitor.visit_operand(op1);
            visitor.visit_operand(op2);
        }
    }
}

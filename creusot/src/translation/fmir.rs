use crate::{backend::place::projection_ty, pearlite::Term, util::ident_of};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{tcx::PlaceTy, BasicBlock, BinOp, Local, ProjectionElem, UnOp},
    ty::{subst::SubstsRef, AdtDef, Ty, TyCtxt},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::VariantIdx;

#[derive(Clone, Debug)]
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
    Assignment(Place<'tcx>, RValue<'tcx>),
    // TODO: Remove `Resolve` and replace it with `Assume`.
    // The reason I have not done this yet is that it would require transforming a `Place` to a `Term`.
    Resolve(DefId, SubstsRef<'tcx>, Place<'tcx>),
    Assertion { cond: Term<'tcx>, msg: String },
    Invariant(Term<'tcx>),
    Variant(Term<'tcx>),
}

// Re-organize this completely
// Get rid of Expr and reimpose a more traditional statement-rvalue-operand setup
#[derive(Clone, Debug)]
pub enum RValue<'tcx> {
    Ghost(Term<'tcx>),
    Borrow(Place<'tcx>),
    Expr(Expr<'tcx>),
}

#[derive(Clone, Debug)]
pub enum Expr<'tcx> {
    Move(Place<'tcx>),
    Copy(Place<'tcx>),
    BinOp(BinOp, Ty<'tcx>, Box<Expr<'tcx>>, Box<Expr<'tcx>>),
    UnaryOp(UnOp, Ty<'tcx>, Box<Expr<'tcx>>),
    Constructor(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    // Should this be a statement?
    Call(DefId, SubstsRef<'tcx>, Vec<Expr<'tcx>>),
    Constant(Term<'tcx>),
    Cast(Box<Expr<'tcx>>, Ty<'tcx>, Ty<'tcx>),
    Tuple(Vec<Expr<'tcx>>),
    Span(Span, Box<Expr<'tcx>>),
    Len(Box<Expr<'tcx>>),
    Array(Vec<Expr<'tcx>>),
    Repeat(Box<Expr<'tcx>>, Box<Expr<'tcx>>),
}

impl<'tcx> Expr<'tcx> {
    pub fn is_call(&self) -> bool {
        match self {
            Expr::Move(_) => false,
            Expr::Copy(_) => false,
            Expr::BinOp(_, _, _, _) => false,
            Expr::UnaryOp(_, _, _) => false,
            Expr::Constructor(_, _, _) => false,
            Expr::Call(_, _, _) => true,
            Expr::Constant(_) => false,
            Expr::Cast(_, _, _) => false,
            Expr::Tuple(_) => false,
            Expr::Span(_, e) => e.is_call(),
            Expr::Len(_) => false,
            Expr::Array(_) => false,
            Expr::Repeat(_, _) => false,
        }
    }

    pub fn is_pure(&self) -> bool {
        match self {
            Expr::Move(_) => true,
            Expr::Copy(_) => true,
            Expr::BinOp(
                BinOp::Add | BinOp::Mul | BinOp::Rem | BinOp::Div | BinOp::Sub,
                _,
                _,
                _,
            ) => false,
            Expr::BinOp(_, _, _, _) => true,
            Expr::UnaryOp(UnOp::Neg, _, _) => false,
            Expr::UnaryOp(_, _, _) => true,
            Expr::Constructor(_, _, es) => es.iter().all(|e| e.is_pure()),
            Expr::Call(_, _, es) => es.iter().all(|e| e.is_pure()),
            Expr::Constant(_) => true,
            Expr::Cast(_, _, _) => false,
            Expr::Tuple(es) => es.iter().all(|e| e.is_pure()),
            Expr::Span(_, e) => e.is_pure(),
            Expr::Len(e) => e.is_pure(),
            Expr::Array(es) => es.iter().all(|e| e.is_pure()),
            Expr::Repeat(l, r) => l.is_pure() && r.is_pure(),
        }
    }
}

#[derive(Clone)]
pub enum Terminator<'tcx> {
    Goto(BasicBlock),
    Switch(Expr<'tcx>, Branches<'tcx>),
    Return,
    Abort,
}

#[derive(Clone)]
pub enum Branches<'tcx> {
    Int(Vec<(i128, BasicBlock)>, BasicBlock),
    Uint(Vec<(u128, BasicBlock)>, BasicBlock),
    Constructor(AdtDef<'tcx>, SubstsRef<'tcx>, Vec<(VariantIdx, BasicBlock)>, BasicBlock),
    Bool(BasicBlock, BasicBlock),
}

#[derive(Clone)]
pub struct Block<'tcx> {
    pub(crate) stmts: Vec<Statement<'tcx>>,
    pub(crate) terminator: Terminator<'tcx>,
}

/// A MIR local along with an optional human-readable name
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LocalIdent {
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

    pub(crate) fn ident(&self) -> why3::Ident {
        self.symbol().to_string().into()
    }

    pub(crate) fn is_anon(&self) -> bool {
        matches!(self, LocalIdent::Anon(_))
    }
}

pub type LocalDecls<'tcx> = IndexMap<Symbol, LocalDecl<'tcx>>;

#[derive(Clone, Debug)]
pub struct LocalDecl<'tcx> {
    // Original MIR local
    pub(crate) mir_local: Local,
    pub(crate) span: Span,
    pub(crate) ty: Ty<'tcx>,
    // Is this a MIR temporary?
    pub(crate) temp: bool,
    // Is this declaration a function argument or return place?
    pub(crate) arg: bool,
}

#[derive(Clone)]
pub struct Body<'tcx> {
    // TODO: Split into return local, args, and true locals?
    // TODO: Remove usage of `LocalIdent`.
    pub(crate) locals: LocalDecls<'tcx>,
    pub(crate) arg_count: usize,
    pub(crate) blocks: IndexMap<BasicBlock, Block<'tcx>>,
}

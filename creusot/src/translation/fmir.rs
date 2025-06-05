use std::collections::HashMap;

use crate::{backend::place::projection_ty, ctx::TranslationCtx, translation::pearlite::Term};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        self, BasicBlock, BinOp, Local, OUTERMOST_SOURCE_SCOPE, Promoted, SourceScope, UnOp,
        tcx::PlaceTy,
    },
    ty::{AdtDef, GenericArgsRef, Ty, TyCtxt},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::VariantIdx;
use why3::Ident;

use super::pearlite::TermKind;

pub(crate) type ProjectionElem<'tcx> = rustc_middle::mir::ProjectionElem<Ident, Ty<'tcx>>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Place<'tcx> {
    pub(crate) local: Ident,
    pub(crate) projections: Box<[ProjectionElem<'tcx>]>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct PlaceRef<'a, 'tcx> {
    pub local: Ident,
    pub projection: &'a [ProjectionElem<'tcx>],
}

impl<'tcx> Place<'tcx> {
    pub(crate) fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> Ty<'tcx> {
        let mut ty = PlaceTy::from_ty(locals[&self.local].ty);

        for p in self.projections.iter() {
            ty = projection_ty(ty, tcx, *p);
        }

        ty.ty
    }

    pub(crate) fn as_symbol(&self) -> Option<Ident> {
        if self.projections.is_empty() { Some(self.local) } else { None }
    }

    pub(crate) fn iter_projections(
        &self,
    ) -> impl DoubleEndedIterator<Item = (PlaceRef<'_, 'tcx>, ProjectionElem<'tcx>)> + '_ {
        self.projections.iter().enumerate().map(move |(i, proj)| {
            let base = PlaceRef { local: self.local, projection: &self.projections[..i] };
            (base, *proj)
        })
    }

    pub fn last_projection(&self) -> Option<(PlaceRef<'_, 'tcx>, ProjectionElem<'tcx>)> {
        if let &[ref proj_base @ .., elem] = &self.projections[..] {
            Some((PlaceRef { local: self.local, projection: proj_base }, elem))
        } else {
            None
        }
    }
}

impl<'tcx> PlaceRef<'_, 'tcx> {
    pub(crate) fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> PlaceTy<'tcx> {
        let mut ty = PlaceTy::from_ty(locals[&self.local].ty);

        for p in self.projection.iter() {
            ty = projection_ty(ty, tcx, *p);
        }

        ty
    }
}

#[derive(Clone, Debug)]
pub enum Statement<'tcx> {
    Assignment(Place<'tcx>, RValue<'tcx>, Span),
    Resolve { did: DefId, subst: GenericArgsRef<'tcx>, pl: Place<'tcx> },
    Assertion { cond: Term<'tcx>, msg: String, trusted: bool },
    // Todo: fold into `Assertion`
    AssertTyInv { pl: Place<'tcx> },
    Call(Place<'tcx>, DefId, GenericArgsRef<'tcx>, Box<[Operand<'tcx>]>, Span),
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

#[derive(Clone, Copy, Debug)]
pub enum TrivialInv {
    Trivial,
    NonTrivial,
}

#[derive(Clone, Debug)]
pub enum RValue<'tcx> {
    Snapshot(Term<'tcx>),
    Borrow(BorrowKind, Place<'tcx>, TrivialInv),
    Operand(Operand<'tcx>),
    ConstBlock(DefId, GenericArgsRef<'tcx>),
    BinOp(BinOp, Operand<'tcx>, Operand<'tcx>),
    UnaryOp(UnOp, Operand<'tcx>),
    Constructor(DefId, GenericArgsRef<'tcx>, Box<[Operand<'tcx>]>),
    Cast(Operand<'tcx>, Ty<'tcx>, Ty<'tcx>),
    Tuple(Box<[Operand<'tcx>]>),
    Len(Operand<'tcx>),
    Array(Box<[Operand<'tcx>]>),
    Repeat(Operand<'tcx>, Operand<'tcx>),
    Ptr(Place<'tcx>),
}

impl RValue<'_> {
    /// Returns false if the expression generates verification conditions
    pub fn is_pure(&self) -> bool {
        match self {
            RValue::Operand(_) => true,
            RValue::ConstBlock(_, _) => false,
            RValue::BinOp(
                BinOp::Add
                | BinOp::AddUnchecked
                | BinOp::Mul
                | BinOp::MulUnchecked
                | BinOp::Rem
                | BinOp::Div
                | BinOp::Sub
                | BinOp::SubUnchecked
                | BinOp::Shl
                | BinOp::ShlUnchecked
                | BinOp::Shr
                | BinOp::ShrUnchecked
                | BinOp::Offset,
                _,
                _,
            ) => false,
            RValue::BinOp(
                BinOp::AddWithOverflow
                | BinOp::SubWithOverflow
                | BinOp::MulWithOverflow
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
                | BinOp::Cmp
                | BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge,
                _,
                _,
            ) => true,
            RValue::UnaryOp(UnOp::Neg, _) => false,
            RValue::UnaryOp(UnOp::Not | UnOp::PtrMetadata, _) => true,
            RValue::Constructor(_, _, _) => true,
            RValue::Cast(_, _, _) => false,
            RValue::Tuple(_) => true,
            RValue::Len(_) => true,
            RValue::Array(_) => true,
            RValue::Repeat(_, _) => true,
            RValue::Snapshot(_) => true,
            RValue::Borrow(_, _, _) => true,
            RValue::Ptr(_) => true,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Operand<'tcx> {
    Move(Place<'tcx>),
    Copy(Place<'tcx>),
    Constant(Term<'tcx>),
    ConstBlock(DefId, GenericArgsRef<'tcx>, Ty<'tcx>),
    Promoted(Promoted, Ty<'tcx>),
}

impl<'tcx> Operand<'tcx> {
    pub fn ty(&self, tcx: TyCtxt<'tcx>, locals: &LocalDecls<'tcx>) -> Ty<'tcx> {
        match self {
            Operand::Move(pl) => pl.ty(tcx, locals),
            Operand::Copy(pl) => pl.ty(tcx, locals),
            Operand::Constant(t) => t.ty,
            Operand::ConstBlock(_, _, ty) => *ty,
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
    Int(Box<[(i128, BasicBlock)]>, BasicBlock),
    Uint(Box<[(u128, BasicBlock)]>, BasicBlock),
    Constructor(
        AdtDef<'tcx>,
        GenericArgsRef<'tcx>,
        Box<[(VariantIdx, BasicBlock)]>,
        Option<BasicBlock>,
    ),
    Bool(BasicBlock, BasicBlock),
}

impl Terminator<'_> {
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

impl Branches<'_> {
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
pub struct Invariant<'tcx> {
    pub(crate) body: Term<'tcx>,
    /// Label ("explanation") for the corresponding Why3 subgoal, including the "expl:" prefix
    pub(crate) expl: String,
}

#[derive(Clone, Debug)]
pub struct Block<'tcx> {
    pub(crate) invariants: Vec<Invariant<'tcx>>,
    pub(crate) variant: Option<Term<'tcx>>,
    pub(crate) stmts: Vec<Statement<'tcx>>,
    pub(crate) terminator: Terminator<'tcx>,
}

pub type LocalDecls<'tcx> = IndexMap<Ident, LocalDecl<'tcx>>;

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
    pub(crate) fresh: usize,
}

/// The scope tree is MIR metadata that we use to map HIR variables (`HirId`)
/// to MIR variables (`Local`, `Place`).
///
/// The MIR we want to translate may contain fragments of Pearlite (from
/// `proof_assert!`, `snapshot!`), whose variables come from `HirId`.
/// We must substitute those variables with their corresponding MIR place.
/// Unfortunately, rustc does not maintain a mapping from `HirId` to MIR
/// places. We recover that information indirectly from scope trees.
///
/// The scope tree is the shape of the binding structure of the HIR term.
/// A node in the scope tree (`SourceScope`) corresponds to a binder in HIR
/// (let, match, closure), and contains a mapping from "source variables"
/// to MIR places. A variable is in scope at a node if it is bound by that
/// node or one of its ancestors.
///
/// Those "source variables" are encoded as `rustc_span::Ident`, which are
/// pairs of string and span. The sad thing is that it is not `HirId`,
/// which would have made things simpler. Because of macros, multiple
/// binders may have the same `rustc_span::Ident`, so we must reimplement
/// the handling of shadowing.
///
/// When we encounter a Pearlite term (from `proof_assert!` or `snapshot!`) in
/// a MIR block, we substitute each free variables as follows: (1) extract
/// `rustc_span::Ident` from its `HirId`, (2) find the closest binder for that
/// `rustc_span::Ident` in the source tree above the `SourceScope` attached to
/// the surrounding MIR block (this is precomputed by `ScopeTree::visible_places`),
/// (3) get the `Place` from that binder to replace the variable.
/// This happens in `inline_pearlite_subst`.
#[derive(Debug)]
pub struct ScopeTree<'tcx>(
    HashMap<SourceScope, (Vec<(rustc_span::Ident, TermKind<'tcx>)>, Option<SourceScope>)>,
);

impl<'tcx> ScopeTree<'tcx> {
    /// Extract the scope tree from a MIR body.
    pub fn build(
        body: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        locals: &HashMap<Local, (Symbol, Ident)>,
    ) -> Self {
        use rustc_middle::mir::VarDebugInfoContents::Place;
        let mut scope_tree: HashMap<
            SourceScope,
            (Vec<(rustc_span::Ident, TermKind<'tcx>)>, Option<_>),
        > = Default::default();

        for var_info in &body.var_debug_info {
            // All variables in the DebugVarInfo should be user variables and thus be just places
            // If the variable is local to the function the place will have no projections.
            // Else this is a captured variable.
            let p = match var_info.value {
                Place(p) => place_to_term(tcx, p, locals, body),
                _ => panic!(),
            };
            let info = var_info.source_info;

            let scope = info.scope;
            let scope_data = &body.source_scopes[scope];

            let entry = scope_tree.entry(scope).or_default();

            let ident = rustc_span::Ident { name: var_info.name, span: var_info.source_info.span };
            entry.0.push((ident, p));

            if let Some(parent) = scope_data.parent_scope {
                entry.1 = Some(parent);
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }

        for (scope, scope_data) in body.source_scopes.iter_enumerated() {
            if let Some(parent) = scope_data.parent_scope {
                scope_tree.entry(scope).or_default().1 = Some(parent);
                scope_tree.entry(parent).or_default();
            } else {
                // Only the argument scope has no parent, because it's the root.
                assert_eq!(scope, OUTERMOST_SOURCE_SCOPE);
            }
        }
        ScopeTree(scope_tree)
    }

    /// Obtain MIR places for HIR variables visible in a given scope.
    pub fn visible_places(&self, scope: SourceScope) -> HashMap<rustc_span::Ident, TermKind<'tcx>> {
        let mut locals = HashMap::new();
        let mut to_visit = Some(scope);

        while let Some(s) = to_visit.take() {
            match self.0.get(&s) {
                None => to_visit = None,
                Some((places, parent)) => {
                    for (id, term) in places {
                        locals.entry(*id).or_insert_with(|| term.clone()); // If multiple binders have the same identifier, use the closest one
                    }
                    to_visit = *parent;
                }
            }
        }

        locals
    }
}

/// Construct a substitution for an inline Pearlite expression (`proof_assert`, `snapshot`).
/// Pearlite identifiers come from HIR (`HirId`), which must correspond to places in the middle of a MIR body.
/// The `places` argument is constructed by `ScopeTree::visible_places`.
///
/// This substitution can't just be represented as a `HashMap` because at this point we don't know its keys,
/// which are the free variables of the Pearlite expression.
pub(crate) fn inline_pearlite_subst<'tcx>(
    tcx: &TranslationCtx<'tcx>,
    places: &HashMap<rustc_span::Ident, TermKind<'tcx>>,
) -> impl Fn(Ident) -> Option<TermKind<'tcx>> {
    |ident| {
        let var = *tcx
            .corenamer
            .borrow()
            .get(&ident)
            .unwrap_or_else(|| panic!("HirId not found for {:?}", ident));
        let ident2 = tcx.tcx.hir().ident(var);
        match places.get(&ident2) {
            Some(term) => Some(term.clone()),
            None => panic!("No place found for {:?}", ident2),
        }
    }
}

/// Translate a place to a term. The place must represent a single named variable, so it can be
/// - A simple `mir::Local`.
/// - A capture. In this case, the place will simply be a local (the capture's envirnoment)
///   followed by
///   + a `Deref` projection if the closure is FnMut.
///   + a `Field` projection.
///   + a `Deref` projection if the capture is mutable.
fn place_to_term<'tcx>(
    tcx: TyCtxt<'tcx>,
    p: mir::Place<'tcx>,
    locals: &HashMap<Local, (Symbol, Ident)>,
    body: &mir::Body<'tcx>,
) -> TermKind<'tcx> {
    let span = body.local_decls[p.local].source_info.span;
    let mut kind = TermKind::Var(locals[&p.local].1.into());
    for (place_ref, proj) in p.iter_projections() {
        let ty = place_ref.ty(&body.local_decls, tcx).ty;
        match proj {
            mir::ProjectionElem::Deref => {
                if ty.is_mutable_ptr() {
                    kind = TermKind::Cur { term: Box::new(Term { ty, span, kind }) };
                } else {
                    kind = TermKind::Coerce { arg: Box::new(Term { ty, span, kind }) }
                }
            }
            mir::ProjectionElem::Field(idx, _) => {
                kind = TermKind::Projection { lhs: Box::new(Term { ty, span, kind }), idx };
            }
            // The rest are impossible for a place generated by a closure capture.
            // FIXME: is this still true in 2021 (with partial captures) ?
            _ => {
                tcx.dcx().struct_span_err(span, "Partial captures are not supported here").emit();
            }
        };
    }
    kind
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

    fn visit_term(&mut self, _: &Term<'tcx>) {}

    fn visit_rvalue(&mut self, rval: &RValue<'tcx>) {
        super_visit_rvalue(self, rval);
    }
}

pub(crate) fn super_visit_body<'tcx, V: FmirVisitor<'tcx>>(visitor: &mut V, body: &Body<'tcx>) {
    for block in &body.blocks {
        visitor.visit_block(block.1);
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
        Operand::Constant(_) | Operand::ConstBlock(_, _, _) | Operand::Promoted(_, _) => (),
    }
}

pub(crate) fn super_visit_place<'tcx, V: FmirVisitor<'tcx>>(_: &mut V, _: &Place<'tcx>) {}

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
        RValue::Snapshot(term) => {
            visitor.visit_term(term);
        }
        RValue::Borrow(_, place, _) => {
            visitor.visit_place(place);
        }
        RValue::Operand(op) => {
            visitor.visit_operand(op);
        }
        RValue::ConstBlock(_, _) => {}
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
        RValue::Ptr(pl) => {
            visitor.visit_place(pl);
        }
    }
}

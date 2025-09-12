use std::path::Path;

use rustc_hir::{HirId, def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{self, FakeReadCause, Location},
    thir::{self, LoopMatchMatchData},
    ty::{self, GenericArgs, GenericArgsRef, TyCtxt, codec::TyDecoder},
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{Span, SpanDecoder};

use crate::options::SpanMode;

pub(crate) fn erased_identity_for_item(tcx: TyCtxt, did: DefId) -> GenericArgsRef {
    tcx.erase_regions(GenericArgs::identity_for_item(tcx, did))
}

pub(crate) fn parent_module(tcx: TyCtxt, mut id: DefId) -> DefId {
    while tcx.def_kind(id) != DefKind::Mod {
        id = tcx.parent(id);
    }
    id
}

pub(crate) fn path_of_span(tcx: TyCtxt, span: Span, span_mode: &SpanMode) -> Option<Box<Path>> {
    if matches!(span_mode, SpanMode::Off) || span.is_dummy() {
        return None;
    }

    let lo = tcx.sess.source_map().lookup_char_pos(span.lo());
    let rustc_span::FileName::Real(path) = &lo.file.name else { return None };
    let path = path.local_path()?;

    if let Some(rustc_base) = &tcx.sess.opts.real_rust_source_base_dir
        && path.starts_with(rustc_base)
    {
        // HACK: don't produce relative paths to standard library
        // HACK: this seems awfully specific to stdlib
        return None;
    }

    Some(path.into())
}

/// A newtype to carry orphan trait impls.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
#[repr(transparent)]
pub struct Orphan<T>(pub T);

fn unorphan<T>(t: Orphan<T>) -> T {
    t.0
}

trait ODecodable<D: Decoder> {
    fn odecode(d: &mut D) -> Self;
}

impl<D: Decoder, T: ODecodable<D>> Decodable<D> for Orphan<T> {
    fn decode(d: &mut D) -> Self {
        Orphan(odecode(d))
    }
}

fn odecode<D: Decoder, T: ODecodable<D>>(d: &mut D) -> T {
    ODecodable::odecode(d)
}
fn decode<D: Decoder, T: Decodable<D>>(d: &mut D) -> T {
    Decodable::decode(d)
}

impl<D: Decoder> ODecodable<D> for Location {
    fn odecode(decoder: &mut D) -> Self {
        let block = decode(decoder);
        let statement_index = decode(decoder);
        Location { block, statement_index }
    }
}

impl<E: Encoder> Encodable<E> for Orphan<Location> {
    fn encode(&self, encoder: &mut E) {
        self.0.block.encode(encoder);
        self.0.statement_index.encode(encoder);
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::Thir<'tcx> {
    fn odecode(d: &mut D) -> Self {
        let body_type = odecode(d);
        let arms = index_vec_unorphan(decode(d));
        let exprs = index_vec_unorphan(decode(d));
        let blocks = index_vec_unorphan(decode(d));
        let stmts = index_vec_unorphan(decode(d));
        let params = index_vec_unorphan(decode(d));
        thir::Thir { body_type, arms, exprs, blocks, stmts, params }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::BodyTy<'tcx> {
    fn odecode(d: &mut D) -> Self {
        match d.read_u8() {
            0 => thir::BodyTy::Const(decode(d)),
            1 => thir::BodyTy::Fn(decode(d)),
            2 => thir::BodyTy::GlobalAsm(decode(d)),
            _ => panic!("invalid discriminant while decoding BodyTy"),
        }
    }
}

fn index_vec_unorphan<K: rustc_index::Idx, V>(
    v: rustc_index::IndexVec<K, Orphan<V>>,
) -> rustc_index::IndexVec<K, V> {
    unsafe { std::mem::transmute(v) }
}

fn option_unorphan<T>(v: Option<Orphan<T>>) -> Option<T> {
    v.map(|Orphan(t)| t)
}

fn box_slice_unorphan<T>(v: Box<[Orphan<T>]>) -> Box<[T]> {
    unsafe { std::mem::transmute(v) }
}

fn vec_unorphan<T>(v: Vec<Orphan<T>>) -> Vec<T> {
    unsafe { std::mem::transmute(v) }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::Arm<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::Arm {
            pattern: odecode(d),
            guard: odecode(d),
            body: odecode(d),
            lint_level: odecode(d),
            scope: decode(d),
            span: decode(d),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::Expr<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::Expr { kind: odecode(d), ty: decode(d), temp_lifetime: odecode(d), span: decode(d) }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::ExprKind<'tcx> {
    fn odecode(d: &mut D) -> Self {
        use decode as m;
        use odecode as o;
        use thir::ExprKind::*;
        match d.read_u8() {
            0 => Scope { region_scope: m(d), lint_level: o(d), value: o(d) },
            1 => Box { value: o(d) },
            2 => If { if_then_scope: m(d), cond: o(d), then: o(d), else_opt: o(d) },
            3 => Call { ty: m(d), fun: o(d), args: o(d), from_hir_call: m(d), fn_span: m(d) },
            4 => ByUse { expr: o(d), span: m(d) },
            5 => Deref { arg: o(d) },
            6 => Binary { op: m(d), lhs: o(d), rhs: o(d) },
            7 => LogicalOp { op: o(d), lhs: o(d), rhs: o(d) },
            8 => Unary { op: m(d), arg: o(d) },
            9 => Cast { source: o(d) },
            10 => Use { source: o(d) },
            11 => NeverToAny { source: o(d) },
            12 => PointerCoercion { cast: m(d), source: o(d), is_from_as_cast: m(d) },
            13 => Loop { body: o(d) },
            14 => LoopMatch { state: o(d), region_scope: m(d), match_data: o(d) },
            15 => Let { expr: o(d), pat: o(d) },
            16 => Match { scrutinee: o(d), arms: o(d), match_source: m(d) },
            17 => Block { block: o(d) },
            18 => Assign { lhs: o(d), rhs: o(d) },
            19 => AssignOp { op: o(d), lhs: o(d), rhs: o(d) },
            20 => Field { lhs: o(d), variant_index: m(d), name: m(d) },
            21 => Index { lhs: o(d), index: o(d) },
            22 => VarRef { id: m(d) },
            23 => UpvarRef { closure_def_id: m(d), var_hir_id: m(d) },
            24 => Borrow { borrow_kind: m(d), arg: o(d) },
            25 => RawBorrow { mutability: m(d), arg: o(d) },
            26 => Break { label: m(d), value: o(d) },
            27 => Continue { label: m(d) },
            28 => ConstContinue { label: m(d), value: o(d) },
            29 => Return { value: o(d) },
            30 => Become { value: o(d) },
            31 => ConstBlock { did: m(d), args: m(d) },
            32 => Repeat { value: o(d), count: m(d) },
            33 => Array { fields: o(d) },
            34 => Tuple { fields: o(d) },
            35 => Adt(o(d)),
            36 => PlaceTypeAscription { source: o(d), user_ty: m(d), user_ty_span: m(d) },
            37 => ValueTypeAscription { source: o(d), user_ty: m(d), user_ty_span: m(d) },
            38 => PlaceUnwrapUnsafeBinder { source: o(d) },
            39 => ValueUnwrapUnsafeBinder { source: o(d) },
            40 => WrapUnsafeBinder { source: o(d) },
            41 => Closure(o(d)),
            42 => Literal { lit: m(d), neg: m(d) },
            43 => NonHirLiteral { lit: m(d), user_ty: m(d) },
            44 => ZstLiteral { user_ty: m(d) },
            45 => NamedConst { def_id: m(d), args: m(d), user_ty: m(d) },
            46 => ConstParam { param: m(d), def_id: m(d) },
            47 => StaticRef { alloc_id: m(d), ty: m(d), def_id: m(d) },
            48 => unimplemented!("decoding InlineAsm"), // InlineAsm(o(d)),
            49 => unimplemented!("decoding OffsetOf"), // OffsetOf { container: m(d), fields: o(d)},
            50 => ThreadLocalRef(m(d)),
            51 => Yield { value: o(d) },
            _ => panic!("invalid discriminant while decoding StmtKind"),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::Block {
    fn odecode(d: &mut D) -> Self {
        thir::Block {
            targeted_by_break: decode(d),
            region_scope: decode(d),
            span: decode(d),
            stmts: box_slice_unorphan(decode(d)),
            expr: option_unorphan(decode(d)),
            safety_mode: odecode(d),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::Stmt<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::Stmt { kind: odecode(d) }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::StmtKind<'tcx> {
    fn odecode(d: &mut D) -> Self {
        match d.read_u8() {
            0 => thir::StmtKind::Let {
                remainder_scope: decode(d),
                init_scope: decode(d),
                pattern: Box::new(odecode(d)),
                initializer: option_unorphan(decode(d)),
                else_block: option_unorphan(decode(d)),
                lint_level: odecode(d),
                span: decode(d),
            },
            1 => thir::StmtKind::Expr { scope: decode(d), expr: odecode(d) },
            _ => panic!("invalid discriminant while decoding StmtKind"),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::Param<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::Param {
            pat: odecode(d),
            ty: decode(d),
            ty_span: decode(d),
            self_kind: decode(d),
            hir_id: decode(d),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::Pat<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::Pat { ty: decode(d), span: decode(d), kind: odecode(d) }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::PatKind<'tcx> {
    fn odecode(d: &mut D) -> Self {
        use thir::PatKind::*;
        match d.read_u8() {
            0 => Missing,
            1 => Wild,
            2 => AscribeUserType { ascription: odecode(d), subpattern: odecode(d) },
            3 => Binding {
                name: decode(d),
                mode: decode(d),
                var: decode(d),
                ty: decode(d),
                subpattern: odecode(d),
                is_primary: decode(d),
            },
            4 => Variant {
                adt_def: decode(d),
                args: decode(d),
                variant_index: decode(d),
                subpatterns: odecode(d),
            },
            5 => Leaf { subpatterns: odecode(d) },
            6 => Deref { subpattern: odecode(d) },
            7 => DerefPattern { subpattern: odecode(d), borrow: decode(d) },
            8 => Constant { value: decode(d) },
            9 => ExpandedConstant { def_id: decode(d), subpattern: odecode(d) },
            10 => Range(std::sync::Arc::new(odecode(d))),
            11 => Slice { prefix: odecode(d), slice: odecode(d), suffix: odecode(d) },
            12 => Array { prefix: odecode(d), slice: odecode(d), suffix: odecode(d) },
            13 => Or { pats: odecode(d) },
            14 => Never,
            15 => panic!("PatKind::Error not decodable"),
            _ => panic!("invalid discriminant for PatKind"),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::Ascription<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::Ascription { annotation: decode(d), variance: decode(d) }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::FieldPat<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::FieldPat { field: decode(d), pattern: odecode(d) }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::PatRange<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::PatRange { lo: odecode(d), hi: odecode(d), end: decode(d), ty: decode(d) }
    }
}
impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::PatRangeBoundary<'tcx> {
    fn odecode(d: &mut D) -> Self {
        use thir::PatRangeBoundary::*;
        match d.read_u8() {
            0 => Finite(decode(d)),
            1 => NegInfinity,
            2 => PosInfinity,
            _ => panic!("invalid discriminant for PatRangeBoundary"),
        }
    }
}

impl<D: Decoder> ODecodable<D> for thir::ExprId {
    fn odecode(d: &mut D) -> Self {
        thir::ExprId::from_u32(d.read_u32())
    }
}

impl<D: Decoder> ODecodable<D> for thir::ArmId {
    fn odecode(d: &mut D) -> Self {
        thir::ArmId::from_u32(d.read_u32())
    }
}

impl<D: Decoder> ODecodable<D> for thir::StmtId {
    fn odecode(d: &mut D) -> Self {
        thir::StmtId::from_u32(d.read_u32())
    }
}

impl<D: Decoder> ODecodable<D> for thir::BlockId {
    fn odecode(d: &mut D) -> Self {
        thir::BlockId::from_u32(d.read_u32())
    }
}

impl<D: SpanDecoder> ODecodable<D> for thir::LintLevel {
    fn odecode(d: &mut D) -> Self {
        match d.read_u8() {
            0 => thir::LintLevel::Inherited,
            1 => thir::LintLevel::Explicit(decode(d)),
            _ => panic!("invalid discriminant while decoding LintLevel"),
        }
    }
}

impl<D: SpanDecoder> ODecodable<D> for thir::BlockSafety {
    fn odecode(d: &mut D) -> Self {
        match d.read_u8() {
            0 => thir::BlockSafety::Safe,
            1 => thir::BlockSafety::BuiltinUnsafe,
            2 => thir::BlockSafety::ExplicitUnsafe(decode(d)),
            _ => panic!("invalid discriminant while decoding BlockSafety"),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::TempLifetime {
    fn odecode(d: &mut D) -> Self {
        thir::TempLifetime { temp_lifetime: decode(d), backwards_incompatible: decode(d) }
    }
}

impl<D: Decoder> ODecodable<D> for thir::LogicalOp {
    fn odecode(d: &mut D) -> Self {
        if d.read_bool() { thir::LogicalOp::And } else { thir::LogicalOp::Or }
    }
}

impl<D: SpanDecoder> ODecodable<D> for thir::LoopMatchMatchData {
    fn odecode(d: &mut D) -> Self {
        thir::LoopMatchMatchData {
            scrutinee: odecode(d),
            arms: box_slice_unorphan(decode(d)),
            span: decode(d),
        }
    }
}

impl<D: Decoder, T: ODecodable<D>> ODecodable<D> for Box<[T]> {
    fn odecode(d: &mut D) -> Self {
        box_slice_unorphan(decode(d))
    }
}

impl<D: Decoder, T: ODecodable<D>> ODecodable<D> for Vec<T> {
    fn odecode(d: &mut D) -> Self {
        vec_unorphan(decode(d))
    }
}

impl<D: Decoder, T: ODecodable<D>> ODecodable<D> for Box<T> {
    fn odecode(d: &mut D) -> Self {
        Box::new(odecode(d))
    }
}

impl<D: Decoder, T: ODecodable<D>> ODecodable<D> for Option<T> {
    fn odecode(d: &mut D) -> Self {
        option_unorphan(decode(d))
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::AdtExpr<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::AdtExpr {
            adt_def: decode(d),
            variant_index: decode(d),
            args: decode(d),
            user_ty: decode(d),
            fields: odecode(d),
            base: odecode(d),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::AdtExprBase<'tcx> {
    fn odecode(d: &mut D) -> Self {
        match d.read_u8() {
            0 => thir::AdtExprBase::None,
            1 => thir::AdtExprBase::Base(odecode(d)),
            2 => thir::AdtExprBase::DefaultFields(decode(d)),
            _ => panic!("invalid discriminant for AdtExprBase"),
        }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::FruInfo<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::FruInfo { base: odecode(d), field_types: decode(d) }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::FieldExpr {
    fn odecode(d: &mut D) -> Self {
        thir::FieldExpr { name: decode(d), expr: odecode(d) }
    }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for thir::ClosureExpr<'tcx> {
    fn odecode(d: &mut D) -> Self {
        thir::ClosureExpr {
            closure_id: decode(d),
            args: odecode(d),
            upvars: odecode(d),
            movability: decode(d),
            fake_reads: vec_unorphan_fst3(decode(d)),
        }
    }
}

fn vec_unorphan_fst3<A, B, C>(v: Vec<(Orphan<A>, B, C)>) -> Vec<(A, B, C)> {
    unsafe { std::mem::transmute(v) }
}

impl<'tcx, D: TyDecoder<'tcx>> ODecodable<D> for ty::UpvarArgs<'tcx> {
    fn odecode(d: &mut D) -> Self {
        use ty::UpvarArgs::*;
        match d.read_u8() {
            0 => Closure(decode(d)),
            1 => Coroutine(decode(d)),
            2 => CoroutineClosure(decode(d)),
            _ => panic!("invalid discriminant for UpvarArgs"),
        }
    }
}

impl<D: Decoder> ODecodable<D> for mir::AssignOp {
    fn odecode(d: &mut D) -> Self {
        use mir::AssignOp::*;
        match d.read_u8() {
            0 => AddAssign,
            1 => SubAssign,
            2 => MulAssign,
            3 => DivAssign,
            4 => RemAssign,
            5 => BitXorAssign,
            6 => BitAndAssign,
            7 => BitOrAssign,
            8 => ShlAssign,
            9 => ShrAssign,
            _ => panic!("invalid discriminant for AssignOp"),
        }
    }
}

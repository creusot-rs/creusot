use std::collections::HashSet;
use std::collections::VecDeque;

use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, subst::InternalSubsts, Ty, TyCtxt, TyKind::*};
use rustc_resolve::Namespace;
use rustc_session::Session;
use rustc_span::Span;
use rustc_span::Symbol;

use crate::mlcfg::QName;
use crate::mlcfg::{TyDecl, Type as MlT};

// Add Sess to this?
pub struct Ctx<'a, 'tcx> {
    translated_tys: HashSet<DefId>,
    tcx: TyCtxt<'tcx>,
    sess: &'a Session,
}

impl<'a, 'tcx> Ctx<'a, 'tcx> {
    // Check whether a type belongs to a binding group which was already translated
    fn type_translated(self: &Self, did: DefId) -> bool {
        self.translated_tys.contains(&did)
    }

    pub fn new(tcx: TyCtxt<'tcx>, sess: &'a Session) -> Self {
        Self { tcx, translated_tys: HashSet::new(), sess }
    }

    fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }
}

use petgraph::graphmap::DiGraphMap;
use petgraph::algo::tarjan_scc;

pub fn check_not_mutally_recursive<'tcx>(ctx: &mut Ctx<'_, 'tcx>, ty_id: DefId, span: Span) {
    let mut graph = DiGraphMap::<_, ()>::new();
    graph.add_node(ty_id);

    let mut to_visit = VecDeque::new();
    to_visit.push_back(ty_id);

    // Construct graph of type dependencies
    while let Some(next) = to_visit.pop_front() {
        let def = ctx.tcx.adt_def(next);
        let substs = InternalSubsts::identity_for_item(ctx.tcx, def.did);

        // TODO: Look up a more efficient way of getting this info
        for variant in &def.variants {
            for field in &variant.fields {
                for ty in field.ty(ctx.tcx, substs).walk() {
                    match ty.expect_ty().kind() {
                        Adt(def, _) => {
                            if ctx.type_translated(def.did) {
                               continue
                            }
                            if !graph.contains_node(def.did) {
                                to_visit.push_back(def.did);
                            }
                            graph.add_edge(next, def.did, ());
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    // Calculate SCCs
    let sccs = tarjan_scc(&graph);
    let group = sccs.last().unwrap();
    assert!(group.contains(&ty_id));

    if group.len() != 1 {
        ctx.crash_and_error(span, "Mutually recursive types are not currently allowed");
    }
}

fn translate_ty_name(ctx: &Ctx<'_, '_>, did: DefId) -> QName {
    super::translate_defid(ctx.tcx, did, Namespace::TypeNS)
}

fn translate_ty_param<'tcx>(p: Symbol) -> String {
    format!("'{}", p.to_string().to_lowercase())
}

// Translate a Rust type declation to an ML one
// Rust tuple-like types are translated as one would expect, to product types in WhyML
// However, Rust struct types are *not* translated to WhyML records, instead we 'forget' the field names
// and also translate them to product types.
//
// Additionally, types are not translated one by one but rather as a *binding group*, so that mutually
// recursive types are properly translated.
pub fn translate_tydecl(ctx: &mut Ctx<'_, '_>, span: Span, did: DefId) -> TyDecl {
    let adt = ctx.tcx.adt_def(did);
    let gens = ctx.tcx.generics_of(did);

    // TODO: allow mutually recursive types
    check_not_mutally_recursive(ctx, did, span);

    // Collect type variables of declaration
    let ty_args: Vec<_> = gens
        .params
        .iter()
        .filter_map(|param| match param.kind {
            ty::GenericParamDefKind::Type { .. } => Some(translate_ty_param(param.name)),
            _ => None,
        })
        .collect();

    let substs = InternalSubsts::identity_for_item(ctx.tcx, did);

    let mut ml_ty_def = Vec::new();

    for var_def in adt.variants.iter() {
        let field_tys: Vec<_> = var_def
            .fields
            .iter()
            .map(|f| f.ty(ctx.tcx, substs))
            .map(|ty| translate_ty(ctx, span, ty))
            .collect();
        log::debug!("{:?}({:?})", var_def.ident, field_tys);

        ml_ty_def.push((var_def.ident.to_string(), field_tys));
    }

    // mark this type as translated
    ctx.translated_tys.insert(did);

    let ty_name = translate_ty_name(ctx, did);
    TyDecl { ty_name, ty_params: ty_args, ty_constructors: ml_ty_def }
}

pub fn translate_ty<'tcx>(ctx: &Ctx<'_, 'tcx>, span: Span, ty: Ty<'tcx>) -> MlT {
    match ty.kind() {
        Bool => MlT::Bool,
        Char => MlT::Char,
        Int(ity) => MlT::Int(*ity),
        Uint(uity) => MlT::Uint(*uity),
        Float(flty) => MlT::Float(*flty),
        Adt(def, s) => {
            if def.is_box() {
                return translate_ty(ctx, span, s[0].expect_ty());
            }
            let args = s.types().map(|t| translate_ty(ctx, span, t)).collect();

            MlT::TApp(box MlT::TConstructor(translate_ty_name(ctx, def.did)), args)
        }
        Tuple(args) => {
            let tys = args.types().map(|t| translate_ty(ctx, span, t)).collect();
            MlT::Tuple(tys)
        }
        Param(p) => MlT::TVar(translate_ty_param(p.name)),
        Ref(_, ty, borkind) => {
            use rustc_ast::Mutability::*;
            match borkind {
                Mut => MlT::MutableBorrow(box translate_ty(ctx, span, ty)),
                Not => translate_ty(ctx, span, ty),
            }
        }
        Never => { MlT::Tuple(vec![])}
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

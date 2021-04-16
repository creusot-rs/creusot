use indexmap::{IndexMap, IndexSet};
use std::collections::VecDeque;

use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Mutability;
use rustc_middle::ty::{self, subst::InternalSubsts, AdtDef, Ty, TyCtxt, TyKind::*, VariantDef};
use rustc_session::Session;
use rustc_span::Span;
use rustc_span::Symbol;

use crate::mlcfg::{Exp as MlE, Pattern, Pattern::*, Predicate, QName, TyDecl, Type as MlT};

use crate::mlcfg::LocalIdent;

pub struct Ctx<'a, 'tcx> {
    translated_tys: IndexSet<DefId>,
    pub tcx: TyCtxt<'tcx>,
    sess: &'a Session,

    results: IndexMap<DefId, (TyDecl, Predicate)>,
}

impl<'a, 'tcx> Ctx<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'a Session) -> Self {
        Self { tcx, translated_tys: IndexSet::new(), sess, results: IndexMap::new() }
    }

    /// Gather the translated types and predicates into a module.
    pub fn collect(self, krate: &mut TranslatedCrate) {
        for (_, (decl, pred)) in self.results {
            krate.add_type(decl, pred);
        }
    }

    fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }
}

/// Translate a Rust type into an MLW one.
pub fn translate_ty<'tcx>(ctx: &mut Ctx<'_, 'tcx>, span: Span, ty: Ty<'tcx>) -> MlT {
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

            if format!("{:?}", def).contains("creusot_contracts::Int") {
                return MlT::Integer;
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
        Slice(ty) => {
            MlT::TApp(box MlT::TConstructor("array".into()), vec![translate_ty(ctx, span, ty)])
        }
        // Slice()
        Never => MlT::Tuple(vec![]),
        _ => ctx.crash_and_error(span, &format!("unsupported type {:?}", ty)),
    }
}

use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;

use super::TranslatedCrate;

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
                    let k = match ty.unpack() {
                        rustc_middle::ty::subst::GenericArgKind::Type(ty) => ty,
                        _ => continue,
                    };
                    if let Adt(def, _) = k.kind() {
                        if !graph.contains_node(def.did) {
                            to_visit.push_back(def.did);
                        }
                        graph.add_edge(next, def.did, ());
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

pub fn translate_ty_name(ctx: &mut Ctx<'_, '_>, did: DefId) -> QName {
    // Check if we've already translated this type before.
    if !ctx.translated_tys.contains(&did) {
        translate_tydecl(ctx, rustc_span::DUMMY_SP, did);
    };
    super::translate_type_id(ctx.tcx, did)
}

fn translate_ty_param(p: Symbol) -> String {
    p.to_string().to_lowercase()
}

// Translate a Rust type declation to an ML one
// Rust tuple-like types are translated as one would expect, to product types in WhyML
// However, Rust struct types are *not* translated to WhyML records, instead we 'forget' the field names
// and also translate them to product types.
//
// Additionally, types are not translated one by one but rather as a *binding group*, so that mutually
// recursive types are properly translated.
// Results are accumulated and can be collected at once by consuming the `Ctx`
pub fn translate_tydecl(ctx: &mut Ctx<'_, '_>, span: Span, did: DefId) {
    // mark this type as translated
    ctx.translated_tys.insert(did);

    // TODO: allow mutually recursive types
    check_not_mutally_recursive(ctx, did, span);

    let adt = ctx.tcx.adt_def(did);
    let gens = ctx.tcx.generics_of(did);

    let ty_name = translate_ty_name(ctx, did);

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
        let field_tys: Vec<_> =
            var_def.fields.iter().map(|f| translate_ty(ctx, span, f.ty(ctx.tcx, substs))).collect();

        let var_name = super::translate_value_id(ctx.tcx, var_def.def_id);
        ml_ty_def.push((var_name.name(), field_tys));
    }

    let pred = drop_pred_decl(ctx, &ty_args, adt, did);

    let ty_decl = TyDecl { ty_name, ty_params: ty_args, ty_constructors: ml_ty_def };
    ctx.results.insert(did, (ty_decl, pred));
}

fn variant_pattern(tcx: TyCtxt<'_>, variant: &VariantDef) -> Pattern {
    let field_pats =
        ('a'..).take(variant.fields.len()).map(|c| VarP(c.to_string().into())).collect();

    let ty_name = super::translate_value_id(tcx, variant.def_id);
    ConsP(ty_name, field_pats)
}

pub fn drop_predicate<'tcx>(ctx: &mut Ctx<'_, 'tcx>, ty: Ty<'tcx>) -> MlE {
    drop_pred_body(ctx, ty, None)
}

fn drop_pred_name<'tcx>(ctx: &mut Ctx<'_, 'tcx>, did: DefId) -> QName {
    let mut name = translate_ty_name(ctx, did);
    name.name.insert(0, "drop".to_owned());
    name
}

// Generate the drop predicate for a specific type
fn drop_pred_decl(
    ctx: &mut Ctx<'_, '_>,
    generics: &[String],
    adt: &AdtDef,
    did: DefId,
) -> Predicate {
    let substs = InternalSubsts::identity_for_item(ctx.tcx, did);
    let mut branches = Vec::new();

    for variant in &adt.variants {
        let drop_fields =
            variant.fields.iter().map(|f| drop_pred_body(ctx, f.ty(ctx.tcx, substs), Some(did)));

        let field_names: Vec<_> = ('a'..).take(variant.fields.len()).collect();

        let drop_variant = field_names
            .iter()
            .map(|c| MlE::Var(c.to_string().into()))
            .zip(drop_fields)
            .map(|(arg, field_drop)| field_drop.app_to(arg))
            .fold_first(MlE::conj)
            .unwrap_or_else(MlE::mk_true);
        branches.push((variant_pattern(ctx.tcx, variant), drop_variant));
    }

    let drop_arg = MlE::Var("self".into());

    let type_drop = if branches.len() == 1 {
        let (pat, variant) = branches.remove(0);
        MlE::Let { pattern: pat, arg: box drop_arg, body: box variant }
    } else {
        MlE::Match(box drop_arg, branches)
    };

    use crate::mlcfg::{Type, Type::*};
    let mut pred_deps: Vec<_> = generics
        .iter()
        .map(|arg| (format!("drop_{}", arg).into(), Type::predicate(TVar(arg.clone()))))
        .collect();

    pred_deps.push((
        "self".into(),
        TApp(
            box TConstructor(translate_ty_name(ctx, did)),
            generics.iter().map(|g| TVar(g.clone())).collect(),
        ),
    ));

    let name = drop_pred_name(ctx, did);

    Predicate { name, args: pred_deps, body: type_drop }
}

/// Create the body for a drop predicate of type `ty` and name `did`.
pub fn drop_pred_body<'tcx>(
    ctx: &mut Ctx<'_, 'tcx>,
    ty: Ty<'tcx>,
    rec_call_did: Option<DefId>,
) -> MlE {
    match ty.kind() {
        Bool => MlE::QVar(crate::mlcfg::drop_bool()),
        Int(_) => MlE::QVar(crate::mlcfg::drop_int()),
        Uint(_) => MlE::QVar(crate::mlcfg::drop_uint()),
        Float(_) => MlE::QVar(crate::mlcfg::drop_float()),
        // Recursive calls should be killed off.
        Adt(def, _) if Some(def.did) == rec_call_did => MlE::QVar(crate::mlcfg::drop_fix()),
        Adt(def, s) if def.is_box() => drop_pred_body(ctx, s[0].expect_ty(), rec_call_did),
        Adt(def, s) => {
            let args = s.types().map(|ty| drop_pred_body(ctx, ty, rec_call_did)).collect();
            let drop_func_name = drop_pred_name(ctx, def.did);
            MlE::Call(box MlE::QVar(drop_func_name), args)
        }
        Tuple(s) => {
            let binder_name: LocalIdent = "tup".into();
            let field_names: Vec<LocalIdent> =
                ('a'..).map(|c| c.to_string().into()).take(s.types().count()).collect();

            let body = s
                .types()
                .zip(field_names.iter())
                .map(|(ty, v)| drop_pred_body(ctx, ty, rec_call_did).app_to(v.clone().into()))
                .fold_first(MlE::conj)
                .unwrap_or_else(MlE::mk_true);

            let field_pat = Pattern::TupleP(field_names.into_iter().map(VarP).collect());

            MlE::Abs(
                binder_name.clone(),
                box MlE::Let { pattern: field_pat, arg: box MlE::Var(binder_name), body: box body },
            )
        }
        Param(s) => MlE::Var(format!("drop_{}", translate_ty_param(s.name)).into()),
        Ref(_, _, Mutability::Mut) => MlE::QVar(crate::mlcfg::drop_mut_ref()),
        Ref(_, _, Mutability::Not) => MlE::QVar(crate::mlcfg::drop_ref()),

        _ => ctx.crash_and_error(
            rustc_span::DUMMY_SP,
            &format!("cannot generate drop predicate for type {:?}", ty),
        ),
    }
}

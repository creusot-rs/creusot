use rustc_errors::DiagnosticId;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, subst::InternalSubsts, AdtDef, Ty, TyCtxt, TyKind::*};
use rustc_resolve::Namespace;
use rustc_session::Session;
use rustc_span::Span;
use rustc_span::Symbol;

use crate::mlcfg::QName;
use crate::mlcfg::{MlTyDecl, Type as MlT};

fn translate_ty_name<'tcx>(tcx: TyCtxt<'tcx>, dif: DefId) -> QName {
    super::translate_defid(tcx, dif, Namespace::TypeNS)
}

fn translate_ty_param<'tcx>(p: Symbol) -> String {
    format!("'{}", p.to_string().to_lowercase())
}

pub fn translate_tydecl<'tcx>(sess: &Session, span: Span, tcx: TyCtxt<'tcx>, adt: &AdtDef) -> MlTyDecl {
    let gens = tcx.generics_of(adt.did);

    let ty_args: Vec<_> = gens
        .params
        .iter()
        .filter_map(|param| match param.kind {
            ty::GenericParamDefKind::Type { .. } => Some(translate_ty_param(param.name)),
            _ => None,
        })
        .collect();

    let substs = InternalSubsts::identity_for_item(tcx, adt.did);

    let mut ml_ty_def = Vec::new();

    for var_def in adt.variants.iter() {
        let field_tys: Vec<_> = var_def
            .fields
            .iter()
            .map(|f| f.ty(tcx, substs))
            .map(|ty| translate_ty(sess, span, tcx, ty))
            .collect();
        log::debug!("{:?}({:?})", var_def.ident, field_tys);

        ml_ty_def.push((var_def.ident.to_string(), field_tys));
    }

    let ty_name = translate_ty_name(tcx, adt.did).unqual_name().to_string();
    MlTyDecl { ty_name, ty_params: ty_args, ty_constructors: ml_ty_def }
}

pub fn translate_ty<'tcx>(sess: &Session, span: Span, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> MlT {
    match ty.kind() {
        Bool => MlT::Bool,
        Char => MlT::Char,
        Int(ity) => MlT::Int(*ity),
        Uint(uity) => MlT::Uint(*uity),
        Float(flty) => MlT::Float(*flty),
        Adt(def, s) => {
            if def.is_box() {
                return translate_ty(sess, span, tcx, s[0].expect_ty());
            }
            let args = s.types().map(|t| translate_ty(sess, span, tcx, t)).collect();

            MlT::TApp(box MlT::TConstructor(translate_ty_name(tcx, def.did)), args)
        }
        Tuple(args) => {
            let tys = args.types().map(|t| translate_ty(sess, span, tcx, t)).collect();
            MlT::Tuple(tys)
        }
        Param(p) => MlT::TVar(translate_ty_param(p.name)),
        Ref(_, ty, borkind) => {
            use rustc_ast::Mutability::*;
            match borkind {
                Mut => MlT::MutableBorrow(box translate_ty(sess, span, tcx, ty)),
                Not => translate_ty(sess, span, tcx, ty),
            }
        }
        Never => { MlT::Tuple(vec![])}
        _ => sess.span_fatal_with_code(span, &format!("unsupported type {:?}", ty), DiagnosticId::Error(String::from("creusot"))),
    }
}

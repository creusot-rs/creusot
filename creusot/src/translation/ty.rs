use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, subst::InternalSubsts, AdtDef, Ty, TyCtxt, TyKind::*};
use rustc_span::Symbol;

use crate::mlcfg::QName;
use crate::mlcfg::{MlTyDecl, Type as MlT};

pub struct TyTranslator<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TyTranslator<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        TyTranslator { tcx }
    }

    fn translate_ty_name(&self, dif: DefId) -> QName {
        super::translate_defid(self.tcx, dif)
    }

    fn translate_ty_param(&self, p: Symbol) -> String {
        format!("'{}", p.to_string().to_lowercase())
    }

    pub fn translate_tydecl(&self, adt: &AdtDef) -> MlTyDecl {
        let gens = self.tcx.generics_of(adt.did);

        let ty_args: Vec<_> = gens
            .params
            .iter()
            .filter_map(|param| match param.kind {
                ty::GenericParamDefKind::Type { .. } => Some(self.translate_ty_param(param.name)),
                _ => None,
            })
            .collect();

        let substs = InternalSubsts::identity_for_item(self.tcx, adt.did);

        let mut ml_ty_def = Vec::new();

        for var_def in adt.variants.iter() {
            let field_tys: Vec<_> = var_def
                .fields
                .iter()
                .map(|f| f.ty(self.tcx, substs))
                .map(|ty| self.translate_ty(ty))
                .collect();
            log::debug!("{:?}({:?})", var_def.ident, field_tys);

            ml_ty_def.push((var_def.ident.to_string(), field_tys));
        }

        let ty_name = self.translate_ty_name(adt.did).unqual_name().to_string();
        MlTyDecl { ty_name, ty_params: ty_args, ty_constructors: ml_ty_def }
    }

    pub fn translate_ty(&self, ty: Ty<'tcx>) -> MlT {
        match ty.kind() {
            Bool => MlT::Bool,
            Char => MlT::Char,
            Int(ity) => MlT::Int(*ity),
            Uint(uity) => MlT::Uint(*uity),
            Float(flty) => MlT::Float(*flty),
            Adt(def, s) => {
                if def.is_box() {
                    return self.translate_ty(s[0].expect_ty());
                }
                let args = s.types().map(|t| self.translate_ty(t)).collect();

                MlT::TApp(box MlT::TConstructor(self.translate_ty_name(def.did)), args)
            }
            Str => unimplemented!("str"),
            Array(_, _) => unimplemented!("array"),
            Slice(_) => unimplemented!("slice"),
            Tuple(args) => {
                let tys = args.types().map(|t| self.translate_ty(t)).collect();
                MlT::Tuple(tys)
            }
            Param(p) => MlT::TVar(self.translate_ty_param(p.name)),
            Ref(_, ty, borkind) => {
                use rustc_ast::Mutability::*;
                match borkind {
                    Mut => MlT::MutableBorrow(box self.translate_ty(ty)),
                    Not => self.translate_ty(ty),
                }
            }
            Never => {
                // TODO: Does why3 have uninhabited types?
                MlT::Tuple(vec![])
            }
            _ => unimplemented!("{:?}", ty),
        }
    }
}

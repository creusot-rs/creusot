
use rustc_middle::ty::{self, AdtDef, Ty, TyKind::*};
use rustc_span::Symbol;

use super::TranslationCtx;

use crate::whycfg::MlCfgType as MlT;


impl<'tcx> TranslationCtx<'tcx> {
  // TODO: actually translate the type declaration
  pub fn translate_tydecl<'a>(&self, adt: &'a AdtDef) -> (&'a AdtDef, Vec<Symbol>) {
    let gens = self.tcx.generics_of(adt.did);

    let ty_args : Vec<_> = gens.params.iter().filter_map(|param| {
      match param.kind {
          ty::GenericParamDefKind::Type { .. } => {Some(param.name)}
          _ => { None }
      }
    }).collect();
    (adt, ty_args)
  }

  pub fn translate_ty(&self, ty: Ty<'tcx>) -> MlT {
    match ty.kind() {
        Bool => {
          MlT::Bool
        }
        Char => {
          unimplemented!()
        }
        Int(ity) => { MlT::Int(*ity) }
        Uint(uity) => { MlT::Uint(*uity) }
        Float(_) => { unimplemented!() }
        Adt(def, s) => {
          if def.is_box() {
            return self.translate_ty(s[0].expect_ty())
          }
          let args = s.types().map(|t| self.translate_ty(t)).collect();

          MlT::TApp(box MlT::TConstructor(self.translate_defid(def.did)), args)
        }
        Str => { unimplemented!("str")}
        Array(_, _) => { unimplemented!("array") }
        Slice(_) => { unimplemented!("slice") }
        Tuple(args) => {
          let tys = args.types().map(|t| self.translate_ty(t)).collect();
          MlT::Tuple(tys)
        }
        Param(_) => { unimplemented!("param") }

        _ => unimplemented!(),
    }
  }
}

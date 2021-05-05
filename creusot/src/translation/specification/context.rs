use std::cell::RefCell;
use std::rc::Rc;

use rustc_hir::def_id::DefId;
use rustc_interface::interface::BoxedResolver;
use rustc_middle::ty::{TyCtxt, TyS};

use pearlite::term;
use pearlite::term::Name;

pub struct RustcResolver<'tcx>(pub Rc<RefCell<BoxedResolver>>, pub DefId, pub TyCtxt<'tcx>);

impl pearlite::parser::Resolver for RustcResolver<'_> {
    fn resolve(&self, path: &[String]) -> Option<pearlite::term::Name> {
        use itertools::*;
        let name = format!("{}", path.iter().format("::"));
        let res = self.0.borrow_mut().access(|resolver| {
            resolver.resolve_str_path_error(
                rustc_span::DUMMY_SP,
                &name,
                rustc_resolve::Namespace::ValueNS,
                self.1,
            )
        });
        match res {
            Ok((_, res)) => Some(defid_to_path(self.2, res.def_id())),
            Err(_) => None,
        }
    }
}

fn def_id_to_id(defid: DefId) -> u64 {
    unsafe { std::mem::transmute(defid) }
}

pub fn id_to_def_id(id: u64) -> DefId {
    unsafe { std::mem::transmute(id) }
}

fn defid_to_path(tcx: TyCtxt<'_>, did: DefId) -> pearlite::term::Name {
    let path = tcx.def_path(did);
    let mut segs = Vec::new();
    use rustc_hir::definitions::DefPathData;

    if path.krate.as_u32() != 0 {
        segs.push(tcx.crate_name(did.krate).to_string())
    }

    for seg in &path.data[..] {
        match seg.data {
            DefPathData::TypeNs(_) | DefPathData::ValueNs(_) => segs.push(seg.to_string()),
            DefPathData::Ctor => {}
            _ => {
                panic!("{:?}", seg)
            }
        }
    }
    let name = segs.pop().unwrap();
    Name::Path { path: segs, name, id: def_id_to_id(did) }
}

pub struct RustcContext<'tcx>(pub TyCtxt<'tcx>);

impl pearlite::typing::GlobalContext for RustcContext<'_> {
    fn resolve_name(&self, path: &term::Name) -> Option<term::Type> {
        if let Name::Path { id, .. } = path {
            let defid: DefId = id_to_def_id(*id);
            Some(ty_to_pearlite(self.0, self.0.type_of(defid)))
        } else {
            None
        }
    }

    fn constructor_type(&self, path: &term::Name) -> Option<(Vec<term::Type>, term::Type)> {
        use term::Type::*;
        match self.resolve_name(path)? {
            Function { args, box res } => Some((args, res)),
            t => Some((vec![], t)),
        }
    }
}

pub fn ty_to_pearlite<'tcx>(tcx: TyCtxt<'tcx>, ty: &TyS<'tcx>) -> pearlite::term::Type {
    use pearlite::term::{LitTy, Type};
    use rustc_middle::ty::TyKind::*;
    use rustc_middle::ty::{IntTy::*, UintTy::*};

    match ty.kind() {
        Bool => Type::Lit(LitTy::Boolean),
        // Char => {}
        Int(size) => match size {
            I8 => Type::Lit(LitTy::I8),
            I16 => Type::Lit(LitTy::I16),
            I32 => Type::Lit(LitTy::I32),
            I64 => Type::Lit(LitTy::I64),
            Isize => Type::Lit(LitTy::ISIZE),
            _ => unimplemented!(),
        },
        Uint(size) => match size {
            U8 => Type::Lit(LitTy::U8),
            U16 => Type::Lit(LitTy::U16),
            U32 => Type::Lit(LitTy::U32),
            U64 => Type::Lit(LitTy::U64),
            Usize => Type::Lit(LitTy::USIZE),
            _ => unimplemented!(),
        },
        FnDef(did, subst) => {
            use rustc_middle::ty::subst::Subst;
            let sig = tcx.normalize_erasing_late_bound_regions(
                rustc_middle::ty::ParamEnv::reveal_all(),
                tcx.fn_sig(*did),
            );
            let sig = sig.subst(tcx, subst);
            Type::Function {
                args: sig.inputs().iter().map(|a| ty_to_pearlite(tcx, a)).collect(),
                res: box ty_to_pearlite(tcx, sig.output()),
            }
        }
        Adt(def, subst) => {
            // hack
            if def.is_box() {
                return Type::Box { ty: box ty_to_pearlite(tcx, subst[0].expect_ty()) };
            }
            if format!("{:?}", def).contains("creusot_contracts::Int") {
                return Type::Lit(LitTy::Integer);
            }

            let args: Vec<_> = subst.types().map(|ty| ty_to_pearlite(tcx, ty)).collect();
            let base = Type::Path { path: defid_to_path(tcx, def.did) };
            Type::App { func: box base, args }
        }
        Ref(_, ty, mutk) => {
            let mutability = match mutk {
                rustc_ast::Mutability::Mut => term::RefKind::Mut,
                rustc_ast::Mutability::Not => term::RefKind::Not,
            };

            term::Type::Reference { kind: mutability, ty: box ty_to_pearlite(tcx, ty) }
        }
        Tuple(tys) => {
            term::Type::Tuple { elems: tys.types().map(|ty| ty_to_pearlite(tcx, ty)).collect() }
        }
        Param(p) => Type::Var(pearlite::term::TyVar(p.index)),
        _ => unimplemented!("{:?}", ty.kind()),
    }
}

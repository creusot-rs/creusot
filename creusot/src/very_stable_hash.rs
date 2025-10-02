use rustc_data_structures::stable_hasher::StableHasher;
use rustc_hashes::Hash64;
use rustc_hir::{
    def_id::{CrateNum, DefId},
    definitions::{DefPath, DefPathData, DisambiguatedDefPathData},
};
use rustc_middle::{ty, ty::TyCtxt};
use rustc_span::Symbol;
use rustc_type_ir::TyKind::*;
use std::hash::{Hash, Hasher};

// HashStable is not stable enough for our purposes
// of hashing ImplSubject to identify Rust impls in the output Coma:
// HashStable depends on the target platform (Linux/Mac/Windows).
//
// The remaining difference is how VeryStableHash hashes identifiers:
// - Symbol is hashed as a string (not as a pointer).
// - CrateNum is hashed as the crate name (not as a number).
// - DefId is hashed as a DefPath
pub trait VeryStableHash<CTX> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher);
}

pub fn get_very_stable_hash<CTX, T: VeryStableHash<CTX> + ?Sized>(t: &T, tcx: &CTX) -> Hash64 {
    let mut hcx = StableHasher::new();
    t.very_stable_hash(tcx, &mut hcx);
    hcx.finish::<Hash64>()
}

// Implementors

// Stdlib types

impl<CTX> VeryStableHash<CTX> for bool {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        hcx.write_u8(*self as u8);
    }
}

impl<CTX> VeryStableHash<CTX> for u32 {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        hcx.write_u32(*self);
    }
}

impl<CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for [T] {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        hcx.write_usize(self.len());
        for item in self {
            item.very_stable_hash(tcx, hcx);
        }
    }
}

impl<CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for Option<T> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            Some(x) => {
                x.very_stable_hash(tcx, hcx);
            }
            None => {}
        }
    }
}

impl<CTX, T: VeryStableHash<CTX>, E: VeryStableHash<CTX>> VeryStableHash<CTX> for Result<T, E> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            Ok(x) => {
                x.very_stable_hash(tcx, hcx);
            }
            Err(e) => {
                e.very_stable_hash(tcx, hcx);
            }
        }
    }
}

impl<CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for Vec<T> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.as_slice().very_stable_hash(tcx, hcx);
    }
}

// Rustc types

impl VeryStableHash<TyCtxt<'_>> for CrateNum {
    // Hash the name of the crate, not the number
    fn very_stable_hash(&self, tcx: &TyCtxt, hcx: &mut StableHasher) {
        tcx.crate_name(*self).very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for DefId {
    // Expand the DefId to a DefPath and hash the path
    fn very_stable_hash(&self, tcx: &TyCtxt, hcx: &mut StableHasher) {
        tcx.def_path(*self).very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for DefPath {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        self.krate.very_stable_hash(tcx, hcx);
        self.data.very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for Symbol {
    // Hash the string, not the pointer
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.as_str().hash(hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for DisambiguatedDefPathData {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.data.very_stable_hash(tcx, hcx);
        self.disambiguator.very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for DefPathData {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        use DefPathData::*;
        match self {
            CrateRoot
            | Impl
            | ForeignMod
            | Use
            | GlobalAsm
            | Closure
            | Ctor
            | AnonConst
            | OpaqueTy
            | SyntheticCoroutineBody
            | NestedStatic => {}
            TypeNs(symbol)
            | ValueNs(symbol)
            | MacroNs(symbol)
            | LifetimeNs(symbol)
            | OpaqueLifetime(symbol)
            | AnonAssocTy(symbol) => symbol.very_stable_hash(tcx, hcx),
        }
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::Ty<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        self.kind().very_stable_hash(tcx, hcx);
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::TyKind<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            Bool => {}
            Char => {}
            Int(int_ty) => int_ty.very_stable_hash(tcx, hcx),
            Uint(int_ty) => int_ty.very_stable_hash(tcx, hcx),
            Float(float_ty) => float_ty.hash(hcx),
            Adt(adt, substs) => {
                adt.did().very_stable_hash(tcx, hcx);
                substs.very_stable_hash(tcx, hcx);
            }
            Foreign(ffi) => ffi.very_stable_hash(tcx, hcx),
            Str => {}
            Array(ty, len) => {
                ty.very_stable_hash(tcx, hcx);
                len.very_stable_hash(tcx, hcx);
            }
            Slice(ty) => ty.very_stable_hash(tcx, hcx),
            RawPtr(ty, m) => {
                ty.very_stable_hash(tcx, hcx);
                m.hash(hcx);
            }
            Ref(reg, ty, m) => {
                reg.very_stable_hash(tcx, hcx);
                ty.very_stable_hash(tcx, hcx);
                m.hash(hcx);
            }
            FnDef(def_id, substs) => {
                def_id.very_stable_hash(tcx, hcx);
                substs.very_stable_hash(tcx, hcx);
            }
            FnPtr(binder, sig) => {
                binder.very_stable_hash(tcx, hcx);
                sig.very_stable_hash(tcx, hcx);
            }
            Dynamic(trait_ty, region) => {
                trait_ty.very_stable_hash(tcx, hcx);
                region.very_stable_hash(tcx, hcx);
            }
            Closure(def_id, substs) => {
                def_id.very_stable_hash(tcx, hcx);
                substs.very_stable_hash(tcx, hcx);
            }
            Coroutine(def_id, substs) => {
                def_id.very_stable_hash(tcx, hcx);
                substs.very_stable_hash(tcx, hcx);
            }
            CoroutineWitness(def_id, substs) => {
                def_id.very_stable_hash(tcx, hcx);
                substs.very_stable_hash(tcx, hcx);
            }
            Tuple(tys) => tys.very_stable_hash(tcx, hcx),
            Never => {}
            Infer(infer_ty) => infer_ty.hash(hcx),
            Alias(ty_kind, ty) => {
                ty_kind.very_stable_hash(tcx, hcx);
                ty.very_stable_hash(tcx, hcx);
            }
            Error(_) => {}
            Pat(ty, pat) => {
                ty.very_stable_hash(tcx, hcx);
                pat.very_stable_hash(tcx, hcx);
            }
            CoroutineClosure(id, args) => {
                id.very_stable_hash(tcx, hcx);
                args.very_stable_hash(tcx, hcx);
            }
            Param(p) => p.very_stable_hash(tcx, hcx),
            Bound(i, _) => i.very_stable_hash(tcx, hcx),
            Placeholder(p) => p.very_stable_hash(tcx, hcx),
            UnsafeBinder(b) => b.very_stable_hash(tcx, hcx),
        }
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::TraitRef<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        self.def_id.very_stable_hash(tcx, hcx);
        self.args.very_stable_hash(tcx, hcx);
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::ExistentialTraitRef<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        self.def_id.very_stable_hash(tcx, hcx);
        self.args.very_stable_hash(tcx, hcx);
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::ExistentialProjection<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        self.def_id.very_stable_hash(tcx, hcx);
        self.args.very_stable_hash(tcx, hcx);
        todo! {"self.term.very_stable_hash(tcx, hcx);"} // Do we want to hash terms
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::ExistentialPredicate<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            ty::ExistentialPredicate::Trait(trait_ref) => trait_ref.very_stable_hash(tcx, hcx),
            ty::ExistentialPredicate::Projection(projection) => {
                projection.very_stable_hash(tcx, hcx)
            }
            ty::ExistentialPredicate::AutoTrait(def_id) => def_id.very_stable_hash(tcx, hcx),
        }
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::PatternKind<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        match self {
            ty::PatternKind::Range { start, end } => {
                start.very_stable_hash(tcx, hcx);
                end.very_stable_hash(tcx, hcx);
            }
            ty::PatternKind::Or(pats) => pats.very_stable_hash(tcx, hcx),
        }
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::Pattern<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        (**self).very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::FnHeader<TyCtxt<'_>> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        self.c_variadic.hash(hcx);
        self.safety.very_stable_hash(tcx, hcx);
        self.abi.very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for rustc_abi::ExternAbi {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        use rustc_abi::ExternAbi::*;
        match self {
            C { unwind }
            | System { unwind }
            | Cdecl { unwind }
            | Stdcall { unwind }
            | Fastcall { unwind }
            | Thiscall { unwind }
            | Vectorcall { unwind }
            | SysV64 { unwind }
            | Win64 { unwind } => unwind.very_stable_hash(tcx, hcx),
            _ => (),
        }
    }
}

impl<CTX> VeryStableHash<CTX> for rustc_hir::Safety {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
    }
}

impl<'ctx, T: VeryStableHash<TyCtxt<'ctx>>> VeryStableHash<TyCtxt<'ctx>> for ty::Binder<'_, T> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'ctx>, hcx: &mut StableHasher) {
        self.as_ref().skip_binder().very_stable_hash(tcx, hcx);
    }
}

impl<'ctx> VeryStableHash<TyCtxt<'ctx>> for ty::FnSigTys<TyCtxt<'ctx>> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'ctx>, hcx: &mut StableHasher) {
        self.inputs_and_output.very_stable_hash(tcx, hcx);
    }
}

impl<'tcx, CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for ty::EarlyBinder<'tcx, T> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.as_ref().skip_binder().very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::AliasTyKind {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::AliasTy<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        self.args.very_stable_hash(tcx, hcx);
        self.def_id.very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::Region<'_> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        self.kind().very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::EarlyParamRegion {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.index.very_stable_hash(tcx, hcx);
        self.name.very_stable_hash(tcx, hcx); // TODO: do we want to hash this?
    }
}

impl<CTX> VeryStableHash<CTX> for ty::DebruijnIndex {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.as_u32().hash(hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::LateParamRegion {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        self.scope.very_stable_hash(tcx, hcx);
        self.kind.very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::LateParamRegionKind {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            ty::LateParamRegionKind::Anon(n) => n.very_stable_hash(tcx, hcx),
            ty::LateParamRegionKind::Named(def_id) => {
                def_id.very_stable_hash(tcx, hcx);
            }
            ty::LateParamRegionKind::ClosureEnv => {}
            ty::LateParamRegionKind::NamedAnon(id, sym) => {
                id.very_stable_hash(tcx, hcx);
                sym.very_stable_hash(tcx, hcx);
            }
        }
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::BoundRegionKind {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            ty::BoundRegionKind::Anon => {}
            ty::BoundRegionKind::Named(id) => {
                id.very_stable_hash(tcx, hcx);
            }
            ty::BoundRegionKind::ClosureEnv => {}
            ty::BoundRegionKind::NamedAnon(sym) => {
                sym.very_stable_hash(tcx, hcx);
            }
        }
    }
}

impl<CTX> VeryStableHash<CTX> for ty::RegionVid {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.as_u32().hash(hcx);
    }
}

impl<CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for ty::Placeholder<T> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.universe.very_stable_hash(tcx, hcx);
        self.bound.very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::UniverseIndex {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.as_u32().hash(hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::BoundVar {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.as_u32().hash(hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::BoundRegion {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        self.var.very_stable_hash(tcx, hcx);
        self.kind.very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::RegionKind<'_> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'_>, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            ty::RegionKind::ReEarlyParam(p) => p.very_stable_hash(tcx, hcx),
            ty::RegionKind::ReBound(debruijn_index, _) => debruijn_index.very_stable_hash(tcx, hcx),
            ty::RegionKind::ReLateParam(p) => p.very_stable_hash(tcx, hcx),
            ty::RegionKind::ReStatic => {}
            ty::RegionKind::ReVar(region_vid) => region_vid.very_stable_hash(tcx, hcx),
            ty::RegionKind::RePlaceholder(p) => p.very_stable_hash(tcx, hcx),
            ty::RegionKind::ReErased => {}
            ty::RegionKind::ReError(_) => {}
        }
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::BoundTy {
    fn very_stable_hash(&self, tcx: &TyCtxt, hcx: &mut StableHasher) {
        self.var.very_stable_hash(tcx, hcx);
        self.kind.very_stable_hash(tcx, hcx);
    }
}

impl VeryStableHash<TyCtxt<'_>> for ty::BoundTyKind {
    fn very_stable_hash(&self, tcx: &TyCtxt, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            ty::BoundTyKind::Anon => {}
            ty::BoundTyKind::Param(def_id) => {
                def_id.very_stable_hash(tcx, hcx);
            }
        }
    }
}

impl<CTX> VeryStableHash<CTX> for ty::ParamTy {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.index.hash(hcx);
        self.name.very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::InferTy {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        todo! {}
    }
}

impl<CTX> VeryStableHash<CTX> for ty::IntTy {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.hash(hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::UintTy {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.hash(hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::FloatTy {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.hash(hcx);
    }
}

impl<CTX, T: VeryStableHash<CTX>> VeryStableHash<CTX> for ty::List<T> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        self.as_slice().very_stable_hash(tcx, hcx);
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::Const<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        self.kind().very_stable_hash(tcx, hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::ScalarInt {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.hash(hcx);
    }
}

impl<CTX> VeryStableHash<CTX> for ty::ValTree<'_> {
    fn very_stable_hash(&self, tcx: &CTX, hcx: &mut StableHasher) {
        let kind = **self;
        std::mem::discriminant(kind).hash(hcx);
        match kind {
            ty::ValTreeKind::Leaf(ty) => ty.very_stable_hash(tcx, hcx),
            ty::ValTreeKind::Branch(b) => b.very_stable_hash(tcx, hcx),
        }
    }
}

impl<CTX> VeryStableHash<CTX> for ty::ParamConst {
    fn very_stable_hash(&self, _tcx: &CTX, hcx: &mut StableHasher) {
        self.index.hash(hcx);
        self.name.hash(hcx);
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::ConstKind<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        std::mem::discriminant(self).hash(hcx);
        match self {
            ty::ConstKind::Unevaluated(unev) => unev.very_stable_hash(tcx, hcx),
            ty::ConstKind::Param(param) => param.very_stable_hash(tcx, hcx),
            ty::ConstKind::Value(v) => {
                v.ty.very_stable_hash(tcx, hcx);
                v.valtree.very_stable_hash(tcx, hcx);
            }
            ty::ConstKind::Infer(_) => todo!(),
            ty::ConstKind::Bound(i, b) => {
                i.very_stable_hash(tcx, hcx);
                b.very_stable_hash(tcx, hcx);
            }
            ty::ConstKind::Placeholder(p) => p.very_stable_hash(tcx, hcx),
            ty::ConstKind::Error(_) => {}
            ty::ConstKind::Expr(_) => todo!(),
        }
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::BoundConst {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        self.var.very_stable_hash(tcx, hcx)
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::UnevaluatedConst<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        self.def.very_stable_hash(tcx, hcx);
        self.args.very_stable_hash(tcx, hcx);
    }
}

impl<'tcx> VeryStableHash<TyCtxt<'tcx>> for ty::GenericArg<'tcx> {
    fn very_stable_hash(&self, tcx: &TyCtxt<'tcx>, hcx: &mut StableHasher) {
        let gak = self.kind();
        std::mem::discriminant(&gak).hash(hcx);
        match gak {
            rustc_type_ir::GenericArgKind::Lifetime(l) => l.very_stable_hash(tcx, hcx),
            rustc_type_ir::GenericArgKind::Type(t) => t.very_stable_hash(tcx, hcx),
            rustc_type_ir::GenericArgKind::Const(c) => c.very_stable_hash(tcx, hcx),
        }
    }
}

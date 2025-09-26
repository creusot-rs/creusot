use std::{hash::Hash as _, path::Path};

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, DefPathHash, LOCAL_CRATE},
    definitions::{DefKey, DefPathData, DisambiguatedDefPathData},
};
use rustc_index::IndexVec;
use rustc_macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_middle::{
    mir::Location,
    thir,
    ty::{self, GenericArgs, GenericArgsRef, TyCtxt},
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::{Span, Symbol};

use creusot_args::options::SpanMode;

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

/// Get the `DefId` of an item given its path as a `String`. It may be a private item.
pub fn forge_def_id<'tcx>(tcx: TyCtxt, path: &[Symbol]) -> Result<DefId, String> {
    let krate_name = path[0];
    let cratenum = if krate_name.as_str() == "crate" {
        LOCAL_CRATE
    } else {
        *tcx.crates(())
            .into_iter()
            .find(|num| krate_name == tcx.crate_name(**num))
            .ok_or_else(|| format!("crate not found: {:?}", krate_name.as_str()))?
    };
    let stable_crate_id = tcx.stable_crate_id(cratenum);
    // Code for hashing `stable_crate_id` from rustc_hir::definitions::Definitions::new
    let hash =
        DefPathHash::new(stable_crate_id, rustc_hashes::Hash64::new(stable_crate_id.as_u64()));
    let len = path.len();
    debug!("forge_def_id: {stable_crate_id:?}");
    forge_def_id_from(
        tcx,
        hash,
        path.into_iter().enumerate().skip(1).map(|(i, &segment)| {
            let data = if i == len - 1 {
                DefPathData::ValueNs(segment)
            } else {
                DefPathData::TypeNs(segment)
            };
            DisambiguatedDefPathData { data, disambiguator: 0 }
        }),
    )
    .ok_or_else(|| format!("item not found: {path:?}"))
}

// Code for hashing `DefPathData` from `Definitions::create_def`
pub fn forge_def_id_from(
    tcx: TyCtxt,
    mut hash: DefPathHash,
    path: impl IntoIterator<Item = DisambiguatedDefPathData>,
) -> Option<DefId> {
    for disambiguated_data in path {
        let parent = tcx.def_path_hash_to_def_id(hash)?;
        debug!("forge_def_id_from: {parent:?}");
        let key = DefKey { parent: Some(parent.index), disambiguated_data };
        hash = compute_stable_hash(key, hash);
    }
    tcx.def_path_hash_to_def_id(hash)
}

fn compute_stable_hash(key: DefKey, parent: DefPathHash) -> DefPathHash {
    let mut hasher = rustc_data_structures::stable_hasher::StableHasher::new();

    // The new path is in the same crate as `parent`, and will contain the stable_crate_id.
    // Therefore, we only need to include information of the parent's local hash.
    parent.local_hash().hash(&mut hasher);

    let DisambiguatedDefPathData { ref data, disambiguator } = key.disambiguated_data;

    std::mem::discriminant(data).hash(&mut hasher);
    if let Some(name) = hashed_symbol(*data) {
        // Get a stable hash by considering the symbol chars rather than
        // the symbol index.
        name.as_str().hash(&mut hasher);
    }

    disambiguator.hash(&mut hasher);

    let local_hash = hasher.finish();

    // Construct the new DefPathHash, making sure that the `crate_id`
    // portion of the hash is properly copied from the parent. This way the
    // `crate_id` part will be recursively propagated from the root to all
    // DefPathHashes in this DefPathTable.
    DefPathHash::new(parent.stable_crate_id(), local_hash)
}

fn hashed_symbol(data: DefPathData) -> Option<Symbol> {
    use DefPathData::*;
    match data {
        TypeNs(name) | ValueNs(name) | MacroNs(name) | LifetimeNs(name) | AnonAssocTy(name)
        | OpaqueLifetime(name) => Some(name),

        Impl
        | ForeignMod
        | CrateRoot
        | Use
        | GlobalAsm
        | Closure
        | Ctor
        | AnonConst
        | OpaqueTy
        | SyntheticCoroutineBody
        | NestedStatic => None,
    }
}

pub fn eq_nameless_generic_args<'tcx>(
    args1: ty::GenericArgsRef<'tcx>,
    args2: ty::GenericArgsRef<'tcx>,
) -> bool {
    NamelessGenericArgs(args1) == NamelessGenericArgs(args2)
}

/// Custom equality on `GenericArgsRef` to ignore the `name` symbol in `Param`.
#[derive(Clone, Copy, Debug, Eq, TypeVisitable, TypeFoldable, TyEncodable, TyDecodable)]
pub struct NamelessGenericArgs<'tcx>(pub ty::GenericArgsRef<'tcx>);

impl<'tcx> From<ty::GenericArgsRef<'tcx>> for NamelessGenericArgs<'tcx> {
    fn from(args: ty::GenericArgsRef<'tcx>) -> Self {
        NamelessGenericArgs(args)
    }
}

impl<'tcx> PartialEq<NamelessGenericArgs<'tcx>> for NamelessGenericArgs<'tcx> {
    fn eq(&self, rhs: &Self) -> bool {
        use rustc_type_ir::GenericArgKind::*;
        self.0.len() == rhs.0.len()
            && self.0.iter().zip(rhs.0).all(|(a, b)| match (a.kind(), b.kind()) {
                (Type(t1), Type(t2)) => equal_types(&t1, &t2),
                (Const(c1), Const(c2)) => equal_const_kinds(c1.kind(), c2.kind()),
                (Lifetime(r1), Lifetime(r2)) => r1 == r2,
                _ => false,
            })
    }
}

fn equal_types<'tcx>(t1: &ty::Ty<'tcx>, t2: &ty::Ty<'tcx>) -> bool {
    use rustc_type_ir::TyKind::*;
    match (t1.kind(), t2.kind()) {
        (Ref(_, ty1, mutable1), Ref(_, ty2, mutable2)) => {
            mutable1 == mutable2 && equal_types(ty1, ty2)
        }
        (Adt(adt1, subst1), Adt(adt2, subst2)) => {
            adt1 == adt2 && NamelessGenericArgs(*subst1).eq(&NamelessGenericArgs(*subst2))
        }
        (Tuple(tys1), Tuple(tys2)) => {
            tys1.len() == tys2.len()
                && tys1.iter().zip(tys2.iter()).all(|(ty1, ty2)| equal_types(&ty1, &ty2))
        }
        (Array(ty1, c1), Array(ty2, c2)) => {
            equal_types(ty1, ty2) && equal_const_kinds(c1.kind(), c2.kind())
        }
        (Slice(ty1), Slice(ty2)) => equal_types(ty1, ty2),
        (RawPtr(ty1, mutable1), RawPtr(ty2, mutable2)) => {
            mutable1 == mutable2 && equal_types(ty1, ty2)
        }
        (FnDef(def_id1, subst1), FnDef(def_id2, subst2)) => {
            def_id1 == def_id2 && NamelessGenericArgs(*subst1) == NamelessGenericArgs(*subst2)
        }
        (Param(p1), Param(p2)) => p1.index == p2.index, // Ignore `name`
        _ => t1 == t2,
    }
}

/// Ignore `name` of `Param`
fn equal_const_kinds<'tcx>(c1: ty::ConstKind<'tcx>, c2: ty::ConstKind<'tcx>) -> bool {
    use rustc_type_ir::ConstKind::Param;
    match (c1, c2) {
        (Param(p1), Param(p2)) => p1.index == p2.index,
        _ => c1 == c2,
    }
}

/// A newtype to carry orphan trait impls.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
#[repr(transparent)]
pub struct Orphan<T>(pub T);

pub trait ODecodable<D: Decoder> {
    fn odecode(d: &mut D) -> Self;
}

pub trait OEncodable<E: Encoder> {
    fn oencode(&self, encoder: &mut E);
}

impl<D: Decoder, T: ODecodable<D>> Decodable<D> for Orphan<T> {
    fn decode(d: &mut D) -> Self {
        Orphan(odecode(d))
    }
}

impl<E: Encoder, T: OEncodable<E>> Encodable<E> for Orphan<T> {
    fn encode(&self, e: &mut E) {
        self.0.oencode(e)
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

impl<E: Encoder> OEncodable<E> for Location {
    fn oencode(&self, encoder: &mut E) {
        self.block.encode(encoder);
        self.statement_index.encode(encoder);
    }
}

fn option_unorphan<T>(v: Option<Orphan<T>>) -> Option<T> {
    v.map(|Orphan(t)| t)
}

fn box_slice_orphan<T>(v: &Box<[T]>) -> &Box<[Orphan<T>]> {
    unsafe { std::mem::transmute(v) }
}

fn box_slice_unorphan<T>(v: Box<[Orphan<T>]>) -> Box<[T]> {
    unsafe { std::mem::transmute(v) }
}

fn vec_unorphan<T>(v: Vec<Orphan<T>>) -> Vec<T> {
    unsafe { std::mem::transmute(v) }
}

fn vec_orphan<T>(v: &Vec<T>) -> &Vec<Orphan<T>> {
    unsafe { std::mem::transmute(v) }
}

impl<D: Decoder> ODecodable<D> for thir::ExprId {
    fn odecode(d: &mut D) -> Self {
        thir::ExprId::from_u32(d.read_u32())
    }
}

impl<E: Encoder> OEncodable<E> for thir::ExprId {
    fn oencode(&self, e: &mut E) {
        e.emit_u32(self.as_u32())
    }
}

impl<D: Decoder, T: ODecodable<D>> ODecodable<D> for Box<[T]> {
    fn odecode(d: &mut D) -> Self {
        box_slice_unorphan(decode(d))
    }
}

impl<E: Encoder, T: OEncodable<E>> OEncodable<E> for Box<[T]> {
    fn oencode(&self, e: &mut E) {
        box_slice_orphan(self).encode(e)
    }
}

impl<D: Decoder, T: ODecodable<D>> ODecodable<D> for Vec<T> {
    fn odecode(d: &mut D) -> Self {
        vec_unorphan(decode(d))
    }
}

impl<E: Encoder, T: OEncodable<E>> OEncodable<E> for Vec<T> {
    fn oencode(&self, e: &mut E) {
        vec_orphan(self).encode(e)
    }
}

impl<D: Decoder, T: ODecodable<D>> ODecodable<D> for Box<T> {
    fn odecode(d: &mut D) -> Self {
        Box::new(odecode(d))
    }
}

impl<E: Encoder, T: OEncodable<E>> OEncodable<E> for Box<T> {
    fn oencode(&self, e: &mut E) {
        (**self).oencode(e)
    }
}

impl<D: Decoder, T: ODecodable<D>> ODecodable<D> for Option<T> {
    fn odecode(d: &mut D) -> Self {
        option_unorphan(decode(d))
    }
}

impl<E: Encoder, T: OEncodable<E>> OEncodable<E> for Option<T> {
    fn oencode(&self, e: &mut E) {
        unsafe { std::mem::transmute::<_, &Option<Orphan<T>>>(self) }.encode(e)
    }
}

impl<E: Encoder, K: rustc_index::Idx, V: OEncodable<E>> OEncodable<E> for IndexVec<K, V> {
    fn oencode(&self, e: &mut E) {
        unsafe { std::mem::transmute::<_, &IndexVec<K, Orphan<V>>>(self) }.encode(e)
    }
}

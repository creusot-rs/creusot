use std::path::Path;

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::Location,
    thir,
    ty::{GenericArgs, GenericArgsRef, TyCtxt},
};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};
use rustc_span::Span;

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

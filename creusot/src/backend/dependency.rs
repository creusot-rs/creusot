use rustc_abi::FieldIdx;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{self, GenericArgKind, GenericArgsRef, List, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_type_ir::AliasTyKind;

use crate::{
    contracts_items::is_size_of_logic,
    ctx::PreMod,
    naming::{
        item_symb, lowercase_prefix, to_alphanumeric, translate_accessor_name, translate_name,
        type_name, value_name,
    },
};

/// Dependencies between items and the resolution logic to find the 'monomorphic' forms accounting
/// for various Creusot hacks like the handling of closures.
///
/// These should be used both to power the cloning system and to order the overall translation of items in Creusot.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, TypeVisitable, TypeFoldable)]
pub(crate) enum Dependency<'tcx> {
    Type(Ty<'tcx>),
    Item(DefId, GenericArgsRef<'tcx>),
    TyInvAxiom(Ty<'tcx>),
    ClosureAccessor(DefId, GenericArgsRef<'tcx>, u32),
    TupleField(&'tcx List<Ty<'tcx>>, FieldIdx),
    PreMod(PreMod),
    Eliminator(DefId, GenericArgsRef<'tcx>),
    DynCast(Ty<'tcx>, Ty<'tcx>),
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn did(self) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        match self {
            Dependency::Item(def_id, subst) => Some((def_id, subst)),
            Dependency::Type(t) => match t.kind() {
                TyKind::Adt(def, substs) => Some((def.did(), substs)),
                TyKind::Closure(id, substs) => Some((*id, substs)),
                TyKind::Alias(AliasTyKind::Opaque | AliasTyKind::Projection, aty) => {
                    Some((aty.def_id, aty.args))
                }
                _ => None,
            },
            _ => None,
        }
    }

    // FIXME: this function should not be necessary, dependencies should not be created non-normalized
    pub(crate) fn erase_regions(self, tcx: TyCtxt<'tcx>) -> Self {
        tcx.erase_regions(self)
    }

    pub(crate) fn base_ident(self, tcx: TyCtxt<'tcx>) -> Option<Symbol> {
        match self {
            Dependency::Type(ty) => match ty.kind() {
                TyKind::Adt(def, _) if !def.is_box() => {
                    Some(item_symb(tcx, def.did(), rustc_hir::def::Namespace::TypeNS))
                }
                TyKind::Alias(AliasTyKind::Opaque, aty) => Some(Symbol::intern(&format!(
                    "opaque{}",
                    tcx.def_path(aty.def_id).data.last().unwrap().disambiguator
                ))),
                TyKind::Alias(AliasTyKind::Projection, aty) => Some(Symbol::intern(&type_name(
                    tcx.opt_item_name(aty.def_id).unwrap_or(Symbol::intern("synthetic")).as_str(),
                ))),
                TyKind::Closure(def_id, _) => Some(Symbol::intern(&format!(
                    "closure{}",
                    tcx.def_path(*def_id).data.last().unwrap().disambiguator
                ))),
                TyKind::Param(p) => Some(Symbol::intern(&type_name(
                    &p.name
                        .as_str()
                        .replace(|c: char| !(c.is_ascii_alphanumeric() || c == '\''), "_"),
                ))),
                TyKind::Tuple(_) => Some(Symbol::intern("tuple")),
                TyKind::Dynamic(_, _, _) => {
                    Some(Symbol::intern(&type_string(tcx, String::new(), ty)))
                }
                _ => None,
            },
            Dependency::Item(did, subst) => match tcx.def_kind(did) {
                DefKind::Impl { .. } => Some(tcx.item_name(tcx.trait_id_of_impl(did).unwrap())),
                DefKind::Closure => Some(Symbol::intern(&format!(
                    "closure{}",
                    tcx.def_path(did).data.last().unwrap().disambiguator
                ))),
                DefKind::Field => {
                    let variant = tcx.parent(did);
                    let name = translate_accessor_name(
                        tcx.item_name(variant).as_str(),
                        tcx.item_name(did).as_str(),
                    );
                    Some(Symbol::intern(&name))
                }
                DefKind::Variant => Some(item_symb(tcx, did, rustc_hir::def::Namespace::ValueNS)),
                _ if is_size_of_logic(tcx, did) => {
                    Some(Symbol::intern(&type_string(tcx, "size_of".into(), subst.type_at(0))))
                }
                DefKind::Const | DefKind::AssocConst | DefKind::ConstParam => {
                    tcx.opt_item_name(did).map(|name| {
                        Symbol::intern(&lowercase_prefix("const_", &translate_name(name.as_str())))
                    })
                }
                _ => tcx
                    .opt_item_name(did)
                    .map(|name| Symbol::intern(&value_name(&translate_name(name.as_str())))),
            },
            Dependency::ClosureAccessor(_, _, ix) => Some(Symbol::intern(&format!("_{ix}"))),
            Dependency::TupleField(_, ix) => Some(Symbol::intern(&format!("_p{}", ix.as_u32()))),
            Dependency::TyInvAxiom(..) => Some(Symbol::intern("inv_axiom")),
            Dependency::Eliminator(did, _) => {
                Some(Symbol::intern(&value_name(&translate_name(tcx.item_name(did).as_str()))))
            }
            Dependency::DynCast(source, target) => Some(Symbol::intern(&type_string(
                tcx,
                type_string(tcx, String::new(), target) + "_of",
                source,
            ))),
            Dependency::PreMod(_) => None,
        }
    }
}

/// Append stringified type to prefix.
///
/// Examples: with `"size_of"` as the prefix,
/// `Option<T>` becomes `"size_of_Option_T"`; `(T, U)` becomes `"size_of_tuple_T_U"`.
///
/// No need to be too rigorous. This is just used to generate more meaningful Why3 identifiers.
fn type_string(tcx: TyCtxt, mut prefix: String, ty: Ty) -> String {
    type_string_walk(tcx, &mut prefix, ty);
    prefix
}

fn type_string_walk(tcx: TyCtxt, prefix: &mut String, ty: Ty) {
    use rustc_type_ir::TyKind::*;
    match ty.kind() {
        Int(int_ty) => push_(prefix, int_ty.name_str()),
        Uint(uint_ty) => push_(prefix, uint_ty.name_str()),
        Float(float_ty) => push_(prefix, float_ty.name_str()),
        Bool => push_(prefix, "bool"),
        Char => push_(prefix, "char"),
        Str => push_(prefix, "str"),
        Array(ty, len) => {
            push_(prefix, "array");
            type_string_walk(tcx, prefix, *ty);
            match len.kind() {
                rustc_type_ir::ConstKind::Value(v)
                    if let ty::ValTreeKind::Leaf(scalar) = *v.valtree =>
                {
                    push_(prefix, &scalar.to_target_usize(tcx).to_string())
                }
                _ => push_(prefix, "n"),
            }
        }
        Slice(ty) => {
            push_(prefix, "slice");
            type_string_walk(tcx, prefix, *ty)
        }
        RawPtr(ty, _) => {
            push_(prefix, "ptr");
            type_string_walk(tcx, prefix, *ty)
        }
        Ref(_, ty, _) => {
            push_(prefix, "ref");
            type_string_walk(tcx, prefix, *ty)
        }
        Tuple(args) if args.is_empty() => {
            push_(prefix, "unit");
        }
        Tuple(args) => {
            push_(prefix, "tup");
            prefix.push_str(&args.len().to_string());
            for ty in args.iter() {
                type_string_walk(tcx, prefix, ty)
            }
        }
        Param(p) => push_(prefix, &to_alphanumeric(p.name.as_str())),
        Adt(def, args) => {
            match tcx.def_key(def.did()).get_opt_name() {
                None => push_(prefix, "x"),
                Some(name) => push_(prefix, &to_alphanumeric(name.as_str())),
            };
            for arg in args.iter() {
                let GenericArgKind::Type(ty) = arg.kind() else { continue };
                type_string_walk(tcx, prefix, ty)
            }
        }
        Alias(_, t) => match tcx.def_key(t.def_id).get_opt_name() {
            None => push_(prefix, "x"),
            Some(name) => push_(prefix, &to_alphanumeric(name.as_str())),
        },
        Dynamic(traits, _, _) => {
            prefix.push_str("dyn");
            for tr in traits.iter() {
                let ty::ExistentialPredicate::Trait(tr) = tr.skip_binder() else { continue };
                let Some(name) = tcx.def_key(tr.def_id).get_opt_name() else { continue };
                push_(prefix, &to_alphanumeric(name.as_str()));
                break;
            }
        }
        _ => push_(prefix, "x"), // Unhandled types appear as "x"
    };
}

fn push_(prefix: &mut String, str: &str) {
    prefix.push('_');
    prefix.push_str(str);
}

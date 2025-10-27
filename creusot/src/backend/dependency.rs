use rustc_abi::FieldIdx;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_macros::{TypeFoldable, TypeVisitable};
use rustc_middle::ty::{GenericArgKind, GenericArgsRef, List, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_type_ir::AliasTyKind;

use crate::{
    contracts_items::Intrinsic,
    ctx::{PreMod, TranslationCtx},
    naming::{ascii_item_name, field_name, lowercase_prefix, type_string, uppercase_prefix},
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
    ResolveAxiom(Ty<'tcx>),
    ClosureAccessor(DefId, GenericArgsRef<'tcx>, u32),
    TupleField(&'tcx List<Ty<'tcx>>, FieldIdx),
    PreMod(PreMod),
    Eliminator(DefId, GenericArgsRef<'tcx>),
    DynCast(Ty<'tcx>, Ty<'tcx>),
    PrivateFields(DefId, GenericArgsRef<'tcx>),
    PrivateResolve(DefId, GenericArgsRef<'tcx>),
    PrivateTyInv(DefId, GenericArgsRef<'tcx>),
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
    pub(crate) fn erase_and_anonymize_regions(self, tcx: TyCtxt<'tcx>) -> Self {
        tcx.erase_and_anonymize_regions(self)
    }

    pub(crate) fn base_ident(self, ctx: &TranslationCtx<'tcx>) -> Option<Symbol> {
        match self {
            Dependency::Type(ty) => Some(Symbol::intern(&lowercase_prefix(
                "t_",
                &type_string(ctx.tcx, String::new(), ty),
            ))),
            Dependency::PrivateFields(did, _) => {
                assert_eq!(ctx.def_kind(did), DefKind::Struct);
                let mut name = lowercase_prefix("t_", ctx.item_name(did).as_str());
                name.push_str("__private");
                Some(Symbol::intern(&name))
            }
            Dependency::Item(did, subst) => match ctx.def_kind(did) {
                DefKind::Closure => Some(Symbol::intern(&format!(
                    "closure{}",
                    ctx.def_key(did).disambiguated_data.disambiguator
                ))),
                DefKind::Field => Some(Symbol::intern(&field_name(ctx.item_name(did).as_str()))),
                DefKind::Variant => {
                    Some(Symbol::intern(&uppercase_prefix("C_", ctx.item_name(did).as_str())))
                }
                _ if Intrinsic::SizeOfLogic.is(ctx, did) => {
                    Some(Symbol::intern(&type_string(ctx.tcx, "size_of".into(), subst.type_at(0))))
                }
                DefKind::Const | DefKind::AssocConst | DefKind::ConstParam => ctx
                    .opt_item_name(did)
                    .map(|name| Symbol::intern(&lowercase_prefix("const_", name.as_str()))),
                _ => {
                    let name = ctx.opt_item_name(did)?;
                    let name = name.as_str();
                    let mut name =
                        lowercase_prefix("f_", name.strip_suffix("_logic").unwrap_or(name));
                    let first_ty = if let Some(parent) = ctx.impl_of_assoc(did)
                        && let Some(trait_ref) = ctx.impl_opt_trait_ref(parent)
                    {
                        // AssocFn in a trait impl: get the instantiated Self type
                        first_ty_arg(trait_ref.instantiate(ctx.tcx, subst).args)
                    } else {
                        // AssocFn in a trait or in an inherent impl: Self is the first argument in `subst`
                        // And for plain fn, also display the first type argument in its name.
                        first_ty_arg(subst)
                    };
                    if let Some(ty) = first_ty {
                        name = type_string(ctx.tcx, name, ty);
                    }
                    Some(Symbol::intern(&name))
                }
            },
            Dependency::ClosureAccessor(_, _, ix) => Some(Symbol::intern(&format!("c{ix}"))),
            Dependency::TupleField(_, ix) => Some(Symbol::intern(&format!("f{}", ix.as_u32()))),
            Dependency::TyInvAxiom(..) => Some(Symbol::intern("inv_axiom")),
            Dependency::ResolveAxiom(..) => Some(Symbol::intern("resolve_axiom")),
            Dependency::Eliminator(did, _) => {
                Some(Symbol::intern(&ascii_item_name("elim_", ctx.tcx, did)))
            }
            Dependency::DynCast(source, target) => Some(Symbol::intern(&type_string(
                ctx.tcx,
                type_string(ctx.tcx, String::new(), target) + "_of",
                source,
            ))),
            Dependency::PreMod(_) => None,
            Dependency::PrivateResolve(..) => Some(Symbol::intern("resolve__private")),
            Dependency::PrivateTyInv(..) => Some(Symbol::intern("inv__private")),
        }
    }
}

fn first_ty_arg(args: GenericArgsRef) -> Option<Ty> {
    args.iter()
        .filter_map(|arg| if let GenericArgKind::Type(ty) = arg.kind() { Some(ty) } else { None })
        .next()
}

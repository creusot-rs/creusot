use heck::ToUpperCamelCase;
use indexmap::{IndexMap, IndexSet};
use rustc_middle::ty::{ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::{Symbol, DUMMY_SP};
use rustc_target::abi::FieldIdx;
use why3::{
    declaration::{CloneSubst, Decl, DeclClone, Use},
    QName,
};

use crate::{
    backend::{self, base_subst, clone_map::cloneable_name, CloneLevel, Why3Generator},
    ctx::TranslationCtx,
    util::{self, get_builtin, inv_module_name, item_name, module_name, ItemType},
};
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
};

use super::{DepNode, Kind, Namer, SymbolKind};

/// Expands the dependencies of a function using Why3's `clone` mechanism.
/// This is the historical way to handle dependencies in Creusot.
pub(super) struct CloneElaborator<'tcx> {
    param_env: ParamEnv<'tcx>,
    name_counts: IndexMap<Symbol, usize>,
    names: IndexMap<DepNode<'tcx>, Info>,
    tcx: TyCtxt<'tcx>,
}

pub struct Info {
    pub(super) kind: Kind,
}

impl<'tcx> CloneElaborator<'tcx> {
    pub fn new(param_env: ParamEnv<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        CloneElaborator {
            param_env,
            name_counts: Default::default(),
            names: Default::default(),
            tcx,
        }
    }
}

impl<'tcx> Namer<'tcx> for CloneElaborator<'tcx> {
    fn value(&mut self, def_id: DefId, subst: rustc_middle::ty::SubstsRef<'tcx>) -> QName {
        let node = DepNode::new(self.tcx, (def_id, subst));
        let name = item_name(self.tcx, def_id, Namespace::ValueNS);

        self.names[&node].kind.qname_ident(name)
    }

    fn ty(&mut self, def_id: DefId, subst: rustc_middle::ty::SubstsRef<'tcx>) -> QName {
        let name = item_name(self.tcx, def_id, Namespace::TypeNS);
        let node = DepNode::new(self.tcx, (def_id, subst));
        if !self.names.contains_key(&node) {
            panic!("missing {node:?}");
        }
        self.names[&node].kind.qname_ident(name.into())
    }

    fn constructor(&mut self, def_id: DefId, subst: rustc_middle::ty::SubstsRef<'tcx>) -> QName {
        let type_id = match self.tcx.def_kind(def_id) {
            DefKind::Closure | DefKind::Struct | DefKind::Enum | DefKind::Union => def_id,
            DefKind::Variant => self.tcx.parent(def_id),
            _ => unreachable!("Not a type or constructor"),
        };
        let mut name = item_name(self.tcx, def_id, Namespace::ValueNS);
        name.capitalize();
        let node = DepNode::new(self.tcx, (type_id, subst));
        self.names[&node].kind.qname_ident(name.into())
    }

    fn accessor(
        &mut self,
        def_id: DefId,
        subst: rustc_middle::ty::SubstsRef<'tcx>,
        variant: usize,
        ix: FieldIdx,
    ) -> QName {
        todo!()
    }

    fn normalize(&self, ctx: &TranslationCtx<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.tcx.try_normalize_erasing_regions(self.param_env, ty).unwrap_or(ty)
    }

    fn import_prelude_module(&mut self, module: backend::PreludeModule) {
        ()
    }

    fn import_builtin_module(&mut self, module: QName) {
        ()
    }
}

impl<'tcx> CloneElaborator<'tcx> {
    pub fn info(&mut self, key: DepNode<'tcx>) -> &Info {
        self.names.entry(key).or_insert_with(|| {
            if let DepNode::Type(ty) = key && !matches!(ty.kind(), TyKind::Alias(_, _)) {
                return if let Some((did, _)) = key.did() {
                    let name = Symbol::intern(&*module_name(self.tcx, did));
                    Info { kind: Kind::Named(name) }
                } else {
                    Info { kind: Kind::Hidden}
                };
            }

            let base = if let DepNode::TyInv(_, inv_kind) = key {
                Symbol::intern(&*inv_module_name(self.tcx, inv_kind))
            } else {
                let did = key.did().unwrap().0;
                let base = match util::item_type(self.tcx, did) {
                    ItemType::Impl => self.tcx.item_name(self.tcx.trait_id_of_impl(did).unwrap()),
                    ItemType::Closure => Symbol::intern(&format!(
                        "closure{}",
                        self.tcx.def_path(did).data.last().unwrap().disambiguator
                    )),
                    _ => self.tcx.item_name(did),
                };
                Symbol::intern(&base.as_str().to_upper_camel_case())
            };

            let count: usize = *self.name_counts.entry(base).and_modify(|c| *c += 1).or_insert(0);
            trace!("inserting {key:?} as {base}{count}");
            Info { kind: Kind::Named(Symbol::intern(&format!("{base}{count}")).into()) }
        })
    }

    pub fn build_clone<'a>(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        item: DepNode<'tcx>,
        deps: impl Iterator<Item = (DepNode<'tcx>, &'a IndexSet<(Kind, SymbolKind)>)>,
        clone_level: CloneLevel,
    ) -> Option<Decl> {
        // Types can't be cloned, but are used (for now).
        if let DepNode::Type(_) = item {
            let (def_id, _) = item.did()?;
            // check if type is not an assoc type
            if util::item_type(ctx.tcx, def_id) == ItemType::Type {
                let use_decl = if let Some(builtin) = get_builtin(ctx.tcx, def_id) {
                    let name = QName::from_string(&builtin.as_str()).unwrap().module_qname();
                    Use { name, as_: None, export: false }
                } else {
                    // HACK for now, eventaully centralize all the name generation
                    let name = self.info(item).kind;
                    let name = cloneable_name(ctx, item, CloneLevel::Body);
                    Use { name: name.clone(), as_: Some(name), export: false }
                };
                return Some(Decl::UseDecl(use_decl));
            }
        }

        let mut clone_subst = base_subst(ctx, self.param_env, self, item);
        trace!("base substs of {item:?}: {clone_subst:?}");

        let outbound: Vec<_> = deps.collect();

        // Grab definitions from all of our dependencies
        for (dep, syms) in outbound {
            trace!("dependency={:?} of={:?} syms={:?}", dep, item, syms);

            match dep {
                DepNode::Type(ty) => {
                    for (nm, sym) in syms.clone() {
                        let ty_name = nm.qname_ident(sym.ident());
                        let ty = backend::ty::translate_ty(ctx, self, DUMMY_SP, ty);
                        clone_subst.push(CloneSubst::Type(ty_name, ty))
                    }
                }
                _ => {
                    // eprintln!("{dep:?}");
                    for (nm, sym) in syms {
                        let elem = sym.to_subst(*nm, self.names[&dep].kind);
                        clone_subst.push(elem);
                    }
                }
            }
        }

        let use_axioms = item.is_inv()
            || item.did().is_some_and(|(def_id, _)| {
                ctx.item(def_id).map(|i| i.has_axioms()).unwrap_or(false)
            });

        if use_axioms {
            clone_subst.push(CloneSubst::Axiom(None))
        }

        // trace!(
        //     "emit clone node={item:?} name={:?} as={:?}",
        //     cloneable_name(ctx, item, clone_level),
        //     self.names[&item].kind.clone()
        // );

        Some(Decl::Clone(DeclClone {
            name: cloneable_name(ctx, item, clone_level),
            subst: clone_subst,
            /// HACK
            kind: self.info(item).kind.into(),
        }))
    }
}

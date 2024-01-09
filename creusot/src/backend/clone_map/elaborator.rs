use heck::ToSnakeCase;
use indexmap::IndexSet;
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
};
use rustc_middle::ty::{self, EarlyBinder, ParamEnv, SubstsRef, Ty, TyCtxt};
use rustc_span::Symbol;
use rustc_target::abi::FieldIdx;

use why3::{
    declaration::{Axiom, Decl, LetDecl, LetKind, Use, ValDecl},
    Ident, QName,
};

use crate::{
    backend::{
        clone_map::cloneable_name, dependency::HackedId, signature::sig_to_why3, term::lower_pure,
        ty_inv::invariant_term, Why3Generator,
    },
    ctx::*,
    translation::{
        function::closure_contract,
        pearlite::{normalize, Term},
        specification::PreContract,
    },
    util::{self, get_builtin, item_name},
};

use super::{CloneNames, DepGraph, DepNode, Kind};

/// The symbol elaborator expands required definitions as symbols and definitions, effectively performing the clones itself.
pub(super) struct SymbolElaborator<'tcx> {
    used_types: IndexSet<DefId>,
    _param_env: ParamEnv<'tcx>,
}

impl<'tcx> SymbolElaborator<'tcx> {
    pub fn new(param_env: ParamEnv<'tcx>) -> Self {
        Self { used_types: Default::default(), _param_env: param_env }
    }

    pub fn build_clone(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut CloneMap<'tcx>,
        _: &DepGraph<'tcx>,
        item: DepNode<'tcx>,
        level_of_item: CloneLevel,
    ) -> Option<Decl> {
        // Types can't be cloned, but are used (for now).
        if let DepNode::Type(_) = item {
            // eprintln!("Cloning type {item:?}");
            let (def_id, _) = item.did()?;
            // check if type is not an assoc type
            if util::item_type(ctx.tcx, def_id) == ItemType::Type {
                let use_decl = self.used_types.insert(def_id).then(|| {
                    if let Some(builtin) = get_builtin(ctx.tcx, def_id) {
                        let name = QName::from_string(&builtin.as_str()).unwrap().module_qname();
                        Use { name, as_: None, export: false }
                    } else {
                        let name = cloneable_name(ctx, item, CloneLevel::Body);
                        Use { name: name.clone(), as_: Some(name), export: false }
                    }
                });
                return use_decl.map(Decl::UseDecl);
            }
        }
        let self_key = names.self_key();

        let old_names = names;
        let mut names = SymNamer {
            tcx: ctx.tcx,
            names: old_names.names.clone(),
            param_env: old_names.param_env(ctx),
        };
        let names = &mut names;

        // let names = old_names;

        if let DepNode::TyInv(ty, kind) = item {
            let term = invariant_term(ctx, ty, kind);
            let exp = lower_pure(ctx, names, term);
            let axiom = Axiom { name: names.ty_inv(ty).name, rewrite: false, axiom: exp };
            return Some(Decl::Axiom(axiom));
        }

        let Some((def_id, subst)) = item.did() else { unreachable!() };

        if util::item_type(ctx.tcx, def_id) == ItemType::AssocTy {
            return Some(ctx.assoc_ty_decl(names, def_id, subst));
        }

        let mut pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone()).subst(ctx.tcx, subst);
        pre_sig = pre_sig.normalize(ctx.tcx, names.param_env);

        let kind = if item.is_hacked() {
            Some(LetKind::Predicate)
        } else {
            util::item_type(ctx.tcx, def_id).let_kind()
        };
        // let names = SymNamer(names.names.clone());
        // let names = &mut & names ;
        // eprintln!("'cloning' {item:?} as name {:?}", names.get(item).ident());

        if CloneLevel::Signature == level_of_item {
            pre_sig.contract = PreContract::default();
        }

        let name = if let DepNode::Hacked(id, def_id, _) = item {
            let closure_contracts = closure_contract(ctx, def_id);
            let name = match id {
                HackedId::PostconditionOnce => {
                    pre_sig = closure_contracts.postcond_once.unwrap().0;
                    names.get(item).ident()
                }
                HackedId::PostconditionMut => {
                    pre_sig = closure_contracts.postcond_mut.unwrap().0;
                    names.get(item).ident()
                }
                HackedId::Postcondition => {
                    pre_sig = closure_contracts.postcond.unwrap().0;
                    names.get(item).ident()
                }
                HackedId::Precondition => {
                    pre_sig = closure_contracts.precond.0;
                    // Ident::build("precondition")
                    names.get(item).ident()
                }
                HackedId::Unnest => {
                    pre_sig = closure_contracts.unnest.unwrap().0;
                    names.get(item).ident()
                }
                HackedId::Resolve => {
                    pre_sig = closure_contracts.resolve.0;
                    names.get(item).ident()
                }
            };

            name
        } else {
            names.value(def_id, subst).name
        };

        let mut sig = sig_to_why3(ctx, names, pre_sig, def_id);
        sig.name = name;
        let ghost = matches!(kind, Some(LetKind::Function | LetKind::Predicate));

        if CloneLevel::Signature == level_of_item {
            let val = ValDecl { ghost, val: true, kind, sig };
            return Some(Decl::ValDecl(val));
        } else if CloneLevel::Contract == level_of_item {
            let val = ValDecl { ghost, val: true, kind, sig };
            return Some(Decl::ValDecl(val));
        };

        if ctx.is_closure(def_id) && !item.is_hacked() {
            return Some(Decl::UseDecl(Use {
                name: format!("{}_Type", &*module_name(ctx.tcx, def_id)).into(),
                as_: Some(names.get(item).ident().into()),
                export: false,
            }));
        }

        if ctx.is_logical(def_id) || item.is_hacked() {
            let term = term(ctx, item)?;
            // let term = ctx.term(def_id)?.clone();

            let mut term = EarlyBinder::bind(term).subst(ctx.tcx, subst);
            normalize(ctx.tcx, names.param_env, &mut term);
            let body = lower_pure(ctx, names, term);

            Some(Decl::Let(LetDecl { kind, sig, rec: false, ghost, body }))
        } else {
            let val = ValDecl { ghost, val: true, kind, sig };
            Some(Decl::ValDecl(val))
        }
    }
}

fn term<'tcx>(ctx: &mut Why3Generator<'tcx>, dep: DepNode<'tcx>) -> Option<Term<'tcx>> {
    if let DepNode::Hacked(hacked_id, id, _) = dep {
        let contracts = closure_contract(ctx, id);
        match hacked_id {
            HackedId::PostconditionOnce => Some(contracts.postcond_once.unwrap().1),
            HackedId::PostconditionMut => Some(contracts.postcond_mut.unwrap().1),
            HackedId::Postcondition => Some(contracts.postcond.unwrap().1),
            HackedId::Precondition => Some(contracts.precond.1),
            HackedId::Unnest => Some(contracts.unnest.unwrap().1),
            HackedId::Resolve => Some(contracts.resolve.1),
        }
    } else {
        ctx.term(dep.did()?.0).cloned()
    }
}

struct SymNamer<'tcx> {
    tcx: TyCtxt<'tcx>,
    names: CloneNames<'tcx>,
    param_env: ParamEnv<'tcx>,
}

impl<'tcx> SymNamer<'tcx> {
    fn get(&self, ix: DepNode<'tcx>) -> &Kind {
        let n = ix.closure_hack(self.tcx);
        self.names.names.get(&n).unwrap_or_else(|| {
            panic!("Could not find {ix:?} -> {n:?}");
        })
    }
}

impl<'tcx> Namer<'tcx> for SymNamer<'tcx> {
    fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let node = DepNode::new(self.tcx, (def_id, subst));
        match self.get(node) {
            Kind::Hidden(id) => id.as_str().into(),
            Kind::Named(nm) => nm.as_str().to_snake_case().into(),
        }
    }

    fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let node = DepNode::new(self.tcx, (def_id, subst));
        let name = self.get(node).ident().into();

        // eprintln!("asked to make type name for {def_id:?} giving {name:?}");
        name
    }

    fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let type_id = match self.tcx.def_kind(def_id) {
            DefKind::Closure | DefKind::Struct | DefKind::Enum | DefKind::Union => def_id,
            DefKind::Variant => self.tcx.parent(def_id),
            _ => unreachable!("Not a type or constructor"),
        };
        let mut name = item_name(self.tcx, def_id, Namespace::ValueNS);
        name.capitalize();
        let node = DepNode::new(self.tcx, (type_id, subst));
        self.get(node).qname_ident(name.into())
    }

    /// Creates a name for a type or closure projection ie: x.field1
    /// This also includes projections from `enum` types
    ///
    /// * `def_id` - The id of the type or closure being projected
    /// * `subst` - Substitution that type is being accessed at
    /// * `variant` - The constructor being used. For closures this is always 0
    /// * `ix` - The field in that constructor being accessed.
    fn accessor(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
        variant: usize,
        ix: FieldIdx,
    ) -> QName {
        let tcx = self.tcx;
        let node = DepNode::new(self.tcx, (def_id, subst));
        let clone = self.get(node);
        let name: Ident = match util::item_type(tcx, def_id) {
            ItemType::Closure => format!("field_{}", ix.as_usize()).into(),
            ItemType::Type => {
                let variant_def = &tcx.adt_def(def_id).variants()[variant.into()];
                let variant = variant_def;
                format!(
                    "{}_{}",
                    variant.name.as_str().to_ascii_lowercase(),
                    variant.fields[ix].name
                )
                .into()
            }
            _ => panic!("accessor: invalid item kind"),
        };

        clone.qname_ident(name.into())
    }

    fn ty_inv(&mut self, ty: Ty<'tcx>) -> QName {
        let def_id =
            self.tcx.get_diagnostic_item(Symbol::intern("creusot_invariant_internal")).unwrap();
        let subst = self.tcx.mk_substs(&[ty::GenericArg::from(ty)]);
        self.value(def_id, subst)
    }

    fn normalize(&self, _: &TranslationCtx<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.tcx.try_normalize_erasing_regions(self.param_env, ty).unwrap_or(ty)

        // self.tcx.try_normalize_erasing_regions(self.param_env(ctx), ty).unwrap_or(ty)
    }

    fn import_prelude_module(&mut self, module: PreludeModule) {
        self.import_builtin_module(module.qname());
    }

    fn import_builtin_module(&mut self, module: QName) {
        self.names.prelude.entry(module).or_insert(false);
    }

    fn with_vis<F, A>(&mut self, _: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        // let public = std::mem::replace(&mut self.dep_level, vis);
        let ret = f(self);
        // self.dep_level = public;
        ret
    }
}

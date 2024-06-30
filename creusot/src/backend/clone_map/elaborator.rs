use crate::{
    backend::{
        dependency::{Dependency, ExtendedId},
        logic::{lower_logical_defn, lower_pure_defn, sigs, spec_axiom},
        program,
        signature::sig_to_why3,
        term::lower_pure,
        ty_inv::InvariantElaborator,
        TransId, Why3Generator,
    },
    ctx::*,
    translation::{
        pearlite::{normalize, Term},
        specification::PreContract,
    },
    util::{self, get_builtin, PreSignature},
};
use indexmap::IndexSet;
use rustc_middle::ty::{self, Const, EarlyBinder, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable};
use rustc_span::{Span, Symbol};
use why3::{
    declaration::{Attribute, Axiom, Constant, Decl, LetKind, Signature, Use, ValDecl},
    QName,
};

use super::{CloneNames, DepNode, Kind};

/// The symbol elaborator expands required definitions as symbols and definitions, effectively performing the clones itself.
pub(super) struct SymbolElaborator<'tcx> {
    used_types: IndexSet<Symbol>,
    _param_env: ParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> SymbolElaborator<'tcx> {
    pub fn new(param_env: ParamEnv<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { used_types: Default::default(), _param_env: param_env, tcx }
    }

    pub fn build_clone(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut Dependencies<'tcx>,
        item: DepNode<'tcx>,
        level_of_item: CloneLevel,
    ) -> Vec<Decl> {
        let param_env = names.param_env(ctx);
        let old_names = names;
        let mut names = SymNamer { tcx: ctx.tcx, param_env, names: &mut old_names.names };
        let names = &mut names;

        match item {
            DepNode::Type(ty) => self.elaborate_ty(ctx, names, ty),
            DepNode::Builtin(b) => {
                vec![Decl::UseDecl(Use { name: b.qname(), as_: None, export: false })]
            }
            DepNode::TyInv(ty, kind) => {
                let term =
                    InvariantElaborator::new(param_env, true).elaborate_inv(ctx, ty, Some(kind));
                let exp = lower_pure(ctx, names, &term);
                let axiom = Axiom { name: names.ty_inv(ty).name, rewrite: false, axiom: exp };
                vec![Decl::Axiom(axiom)]
            }
            DepNode::Item(_, _) | DepNode::Hacked(_, _, _) => {
                self.elaborate_item(ctx, names, param_env, level_of_item, item)
            }
        }
    }

    fn elaborate_ty(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut SymNamer<'_, 'tcx>,
        ty: Ty<'tcx>,
    ) -> Vec<Decl> {
        let Some((def_id, subst)) = DepNode::Type(ty).did() else { return Vec::new() };

        match ty.kind() {
            TyKind::Alias(_, _) => vec![ctx.assoc_ty_decl(names, def_id, subst)],
            _ => {
                if let Some(why3_modl) = util::get_builtin(ctx.tcx, def_id) {
                    let qname = QName::from_string(why3_modl.as_str()).unwrap();
                    let Kind::Used(modl, _) = names.insert(DepNode::Type(ty)) else {
                        return vec![];
                    };

                    self.used_types
                        .insert(modl)
                        .then(|| {
                            let use_decl =
                                Use { as_: None, name: qname.module_qname(), export: false };

                            vec![Decl::UseDecl(use_decl)]
                        })
                        .unwrap_or_default()
                } else {
                    self.emit_use(names, DepNode::Type(ty))
                }
            }
        }
    }

    fn emit_use(&mut self, names: &mut SymNamer<'_, 'tcx>, dep: Dependency<'tcx>) -> Vec<Decl> {
        if let k @ Kind::Used(modl, _) = names.insert(dep) {
            self.used_types
                .insert(modl)
                .then(|| {
                    let qname = k.qname();
                    let name = qname.module_qname();
                    let mut did = dep.did().unwrap().0;
                    if util::item_type(self.tcx, did) == ItemType::Field {
                        did = self.tcx.parent(did);
                    };

                    let modl = if util::item_type(self.tcx, did) == ItemType::Closure {
                        Symbol::intern(&format!("{}_Type", module_name(self.tcx, did)))
                    } else {
                        module_name(self.tcx, did)
                    };

                    let use_decl =
                        Use { as_: Some(name.clone()), name: modl.as_str().into(), export: false };
                    vec![Decl::UseDecl(use_decl)]
                })
                .unwrap_or_default()
        } else {
            vec![]
        }
    }

    fn elaborate_item(
        &mut self,
        ctx: &mut Why3Generator<'tcx>,
        names: &mut SymNamer<'_, 'tcx>,
        param_env: ParamEnv<'tcx>,
        level_of_item: CloneLevel,
        item: DepNode<'tcx>,
    ) -> Vec<Decl> {
        let Some((def_id, subst)) = item.did() else { unreachable!("{item:?}") };

        if let Some(b) = get_builtin(ctx.tcx, def_id) {
            return vec![Decl::UseDecl(Use {
                name: QName::from_string(b.as_str()).unwrap().module_qname(),
                as_: None,
                export: false,
            })];
        }

        if let Kind::Used(_, _) = names.get(item) {
            return self.emit_use(names, item);
        };

        let mut pre_sig = EarlyBinder::bind(sig(ctx, item)).instantiate(ctx.tcx, subst);
        pre_sig = pre_sig.normalize(ctx.tcx, param_env);

        let is_accessor = item.to_trans_id().is_some_and(|i| ctx.is_accessor(i));
        let kind = if item.is_hacked() {
            if is_accessor {
                Some(LetKind::Function)
            } else {
                Some(LetKind::Predicate)
            }
        } else {
            util::item_type(ctx.tcx, def_id).let_kind()
        };

        // eprintln!("{item:?} {kind:?}");

        if CloneLevel::Signature == level_of_item {
            pre_sig.contract = PreContract::default();
        }

        let name = if let DepNode::Hacked(_, _, _) = item {
            names.insert(item).ident()
        } else {
            names.value(def_id, subst).name
        };

        let mut sig = sig_to_why3(ctx, names, &pre_sig, def_id);
        sig.name = name;

        if CloneLevel::Signature == level_of_item {
            return val(ctx, sig, kind);
        } else if CloneLevel::Contract == level_of_item {
            return val(ctx, sig, kind);
        };

        if item.is_hacked() || ctx.is_logical(def_id) {
            let Some(term) = term(ctx, item) else { return Vec::new() };
            let mut term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
            normalize(ctx.tcx, param_env, &mut term);
            if is_accessor {
                lower_logical_defn(ctx, names, sig, kind, term)
            } else if item.is_hacked() {
                // TODO: Clean this up and merge with previous branches
                lower_pure_defn(ctx, names, sig, kind, false, term)
            } else {
                lower_logical_defn(ctx, names, sig, kind, term)
            }
        } else if util::item_type(ctx.tcx, def_id) == ItemType::Constant {
            let uneval = ty::UnevaluatedConst::new(def_id, subst);
            let constant = Const::new(
                ctx.tcx,
                ty::ConstKind::Unevaluated(uneval),
                ctx.type_of(def_id).instantiate_identity(),
            );

            let span = ctx.def_span(def_id);
            let res = crate::constant::from_ty_const(&mut ctx.ctx, constant, param_env, span);

            let res = lower_pure(ctx, names, &res);
            vec![Decl::ConstantDecl(Constant {
                type_: sig.retty.unwrap(),
                name: sig.name,
                body: res,
            })]
        } else {
            val(ctx, sig, kind)
        }
    }
}

fn val<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    mut sig: Signature,
    kind: Option<LetKind>,
) -> Vec<Decl> {
    sig.contract.variant = Vec::new();
    if let Some(k) = kind {
        let ax = if !sig.contract.is_empty() { Some(spec_axiom(&sig)) } else { None };

        let (mut sig, prog_sig) = sigs(ctx, sig);
        if let LetKind::Predicate = k {
            sig.retty = None;
        };

        if let LetKind::Constant = k {
            return vec![Decl::ValDecl(ValDecl { ghost: false, val: false, kind, sig })];
        }

        let mut d = vec![
            Decl::ValDecl(ValDecl { ghost: false, val: false, kind, sig }),
            program::val(ctx, prog_sig),
        ];

        if let Some(ax) = ax {
            d.push(Decl::Axiom(ax))
        }
        d
    } else {
        vec![program::val(ctx, sig)]
    }
}

fn term<'tcx>(ctx: &mut Why3Generator<'tcx>, dep: DepNode<'tcx>) -> Option<Term<'tcx>> {
    ctx.term(dep.to_trans_id()?).cloned()
}

fn sig<'tcx>(ctx: &mut Why3Generator<'tcx>, dep: DepNode<'tcx>) -> PreSignature<'tcx> {
    match dep.to_trans_id().unwrap() {
        TransId::Item(id) => ctx.sig(id).clone(),
        // In future change this
        TransId::TyInv(_) => unreachable!(),
        TransId::Hacked(h_id, id) => match h_id {
            ExtendedId::PostconditionOnce => {
                ctx.closure_contract(id).postcond_once.as_ref().unwrap().0.clone()
            }
            ExtendedId::PostconditionMut => {
                ctx.closure_contract(id).postcond_mut.as_ref().unwrap().0.clone()
            }
            ExtendedId::Postcondition => {
                ctx.closure_contract(id).postcond.as_ref().unwrap().0.clone()
            }
            ExtendedId::Precondition => ctx.closure_contract(id).precond.0.clone(),
            ExtendedId::Unnest => ctx.closure_contract(id).unnest.as_ref().unwrap().0.clone(),
            ExtendedId::Resolve => ctx.closure_contract(id).resolve.0.clone(),
            ExtendedId::Accessor(ix) => ctx.closure_contract(id).accessors[ix as usize].0.clone(),
        },
    }
}

struct SymNamer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    names: &'a mut CloneNames<'tcx>,
    param_env: ParamEnv<'tcx>,
}

impl<'a, 'tcx> SymNamer<'a, 'tcx> {
    fn get(&self, ix: DepNode<'tcx>) -> &Kind {
        let n = ix.closure_hack(self.tcx);
        let n = self.tcx.try_normalize_erasing_regions(self.param_env, n).unwrap_or(n);
        self.names.names.get(&n).unwrap_or_else(|| {
            panic!("Could not find {ix:?} -> {n:?}");
        })
    }
}

impl<'a, 'tcx> Namer<'tcx> for SymNamer<'a, 'tcx> {
    fn insert(&mut self, ix: DepNode<'tcx>) -> Kind {
        *self.get(ix)
    }

    fn normalize<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(
        &self,
        _: &TranslationCtx<'tcx>,
        ty: T,
    ) -> T {
        self.tcx.try_normalize_erasing_regions(self.param_env, ty).unwrap_or(ty)
    }

    fn import_prelude_module(&mut self, _: PreludeModule) {
        ()
    }

    fn with_vis<F, A>(&mut self, _: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        f(self)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn span(&mut self, span: Span) -> Option<Attribute> {
        if span.is_dummy() {
            return None;
        }
        let cnt = self.names.spans.len();
        let name =
            self.names.spans.entry(span).or_insert_with(|| Symbol::intern(&format!("span{cnt}")));
        Some(Attribute::NamedSpan(name.to_string()))
    }
}

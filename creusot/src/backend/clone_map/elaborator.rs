use heck::ToSnakeCase;
use indexmap::IndexSet;
use rustc_hir::{
    def::{DefKind, Namespace},
    def_id::DefId,
};
use rustc_middle::ty::{self, EarlyBinder, ParamEnv, SubstsRef, Ty, TyCtxt, TyKind};
use rustc_span::Symbol;
use rustc_target::abi::FieldIdx;

use why3::{
    declaration::{Axiom, Decl, LetDecl, LetKind, Predicate, Signature, Use, ValDecl},
    Ident, QName,
};

use crate::{
    backend::{
        dependency::HackedId,
        logic::{lower_body_term, sigs, spec_axiom},
        program::{int_to_prelude, uint_to_prelude},
        signature::sig_to_why3,
        term::lower_pure,
        ty_inv::elaborate_inv,
        TransId, Why3Generator,
    },
    ctx::*,
    translation::{
        fmir::LocalDecls,
        pearlite::{normalize, Term},
        specification::PreContract,
    },
    util::{self, get_builtin, item_name, PreSignature},
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
    ) -> Vec<Decl> {
        // Types can't be cloned, but are used (for now).
        if let DepNode::Type(ty) = item {
            // eprintln!("Cloning type {item:?}");
            let Some((def_id, subst)) = item.did() else {
                match ty.kind() {
                    TyKind::Int(ity) => names.import_prelude_module(int_to_prelude(*ity)),
                    TyKind::Uint(uty) => names.import_prelude_module(uint_to_prelude(*uty)),
                    _ => (),
                }
                return Vec::new()
            };
            // check if type is not an assoc type
            if util::item_type(ctx.tcx, def_id) != ItemType::AssocTy {
                let use_decl = self.used_types.insert(def_id).then(|| {
                    if let Some(builtin) = get_builtin(ctx.tcx, def_id) {
                        let name = QName::from_string(&builtin.as_str()).unwrap().module_qname();
                        Use { name, as_: None, export: false }
                    } else {
                        let name = names.ty(def_id, subst);
                        let name = name.module_qname();
                        let mod_name = if util::item_type(ctx.tcx, def_id) == ItemType::Closure {
                            format!("{}_Type", &*module_name(ctx.tcx, def_id)).into()
                        } else {
                            module_name(ctx.tcx, def_id)
                        };
                        Use { name: mod_name.into(), as_: Some(name), export: false }
                    }
                });
                return use_decl.into_iter().map(Decl::UseDecl).collect();
            }
        }
        // let self_key = names.self_key();

        let old_names = names;
        let mut names = SymNamer {
            tcx: ctx.tcx,
            names: old_names.names.clone(),
            param_env: old_names.param_env(ctx),
        };
        let names = &mut names;

        let param_env = old_names.param_env(ctx);

        // let names = old_names;

        if let DepNode::TyInv(ty, kind) = item {
            // eprintln!("Elaborating invariant {item:?}");
            let term = elaborate_inv(ctx, param_env, ty, Some(kind));
            let exp = lower_pure(ctx, names, term);
            let axiom = Axiom { name: names.ty_inv(ty).name, rewrite: false, axiom: exp };
            return vec![Decl::Axiom(axiom)];
        }

        if let DepNode::Buitlin(b) = item {
            return vec![Decl::UseDecl(Use { name: b.qname(), as_: None, export: false })];
        }

        let Some((def_id, subst)) = item.did() else { unreachable!("{item:?}") };

        if let Some(b) = get_builtin(ctx.tcx, def_id) {
            return vec![Decl::UseDecl(Use {
                name: QName::from_string(b.as_str()).unwrap().module_qname(),
                as_: None,
                export: false,
            })];
        }

        let is_accessor = item.to_trans_id().is_some_and(|i| ctx.is_accessor(i));
        if util::item_type(ctx.tcx, def_id) == ItemType::AssocTy {
            return vec![ctx.assoc_ty_decl(names, def_id, subst)];
        }

        let mut pre_sig = EarlyBinder::bind(sig(ctx, item)).subst(ctx.tcx, subst);
        pre_sig = pre_sig.normalize(ctx.tcx, param_env);

        let kind = if item.is_hacked() {
            if is_accessor {
                Some(LetKind::Function)
            } else {
                Some(LetKind::Predicate)
            }
        } else {
            util::item_type(ctx.tcx, def_id).let_kind()
        };
        // let names = SymNamer(names.names.clone());
        // let names = &mut & names ;
        // assert!(!petgraph::algo::is_cyclic_directed(&deps.graph));
        // eprintln!("'cloning' {item:?} as name {:?}", names.get(item).ident());

        if CloneLevel::Signature == level_of_item {
            pre_sig.contract = PreContract::default();
        }

        let name = if let DepNode::Hacked(_, _, _) = item {
            names.insert(item).ident()
        } else {
            names.value(def_id, subst).name
        };

        let mut sig = sig_to_why3(ctx, names, pre_sig, def_id);
        sig.name = name;
        let ghost = matches!(kind, Some(LetKind::Function | LetKind::Predicate)) && !is_accessor;

        // eprintln!("{item:?} at {level_of_item:?}");

        if CloneLevel::Signature == level_of_item {
            return val(ctx, sig, kind, ghost);
        } else if CloneLevel::Contract == level_of_item {
            return val(ctx, sig, kind, ghost);
        };

        if item.is_hacked() {
            let Some(mut term) = term(ctx, item) else { return Vec::new() };
            normalize(ctx.tcx, param_env, &mut term);
            let body = lower_pure(ctx, names, term);
            if let Some(LetKind::Predicate) = kind {
                sig.retty = None
            };

            match kind.unwrap() {
                LetKind::Function => {
                    vec![Decl::Let(LetDecl { kind, sig, rec: false, ghost: false, body })]
                }

                // vec![Decl::LogicDefn(Logic { sig, body })],
                LetKind::Predicate => vec![Decl::PredDecl(Predicate { sig, body })],
                _ => unreachable!(),
            }
        } else if ctx.is_logical(def_id) {
            let Some(term) = term(ctx, item) else { return Vec::new() };
            // let term = ctx.term(def_id)?.clone();

            let mut term = EarlyBinder::bind(term).subst(ctx.tcx, subst);
            normalize(ctx.tcx, param_env, &mut term);

            // eprintln!("{term:?}");
            // if ghost && body.is_pure() {
            //     body = Exp::Pure(Box::new(body))
            // }

            let d = lower_body_term(ctx, names, sig, term, def_id);
            old_names.names.prelude.extend(names.names.prelude.clone());
            d
        } else if util::item_type(ctx.tcx, def_id) == ItemType::Constant {
            let uneval = ty::UnevaluatedConst::new(def_id, subst);
            let constant = ctx
                .mk_const(ty::ConstKind::Unevaluated(uneval), ctx.type_of(def_id).subst_identity());

            let param_env = ctx.param_env(def_id);
            let span = ctx.def_span(def_id);
            let res = crate::constant::from_ty_const(&mut ctx.ctx, constant, param_env, span);
            let res = res.to_why(ctx, names, &LocalDecls::new());

            vec![Decl::Let(LetDecl {
                kind: Some(LetKind::Constant),
                sig: sig.clone(),
                rec: false,
                ghost: false,
                body: res,
            })]
            // vec![Decl::Let(LetDecl { kind, sig, rec: false, ghost, body })]
        } else {
            val(ctx, sig, kind, ghost)
        }
    }
}

fn val<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    mut sig: Signature,
    kind: Option<LetKind>,
    ghost: bool,
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
            Decl::ValDecl(ValDecl { ghost: false, val: true, kind: None, sig: prog_sig }),
        ];

        if let Some(ax) = ax {
            d.push(Decl::Axiom(ax))
        }
        d
    } else {
        // Program signature
        vec![Decl::ValDecl(ValDecl { ghost, val: true, kind, sig })]
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
            HackedId::PostconditionOnce => {
                ctx.closure_contract(id).postcond_once.as_ref().unwrap().0.clone()
            }
            HackedId::PostconditionMut => {
                ctx.closure_contract(id).postcond_mut.as_ref().unwrap().0.clone()
            }
            HackedId::Postcondition => {
                ctx.closure_contract(id).postcond.as_ref().unwrap().0.clone()
            }
            HackedId::Precondition => ctx.closure_contract(id).precond.0.clone(),
            HackedId::Unnest => ctx.closure_contract(id).unnest.as_ref().unwrap().0.clone(),
            HackedId::Resolve => ctx.closure_contract(id).resolve.0.clone(),
            HackedId::Accessor(ix) => ctx.closure_contract(id).accessors[ix as usize].0.clone(),
        },
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
        let n = self.tcx.try_normalize_erasing_regions(self.param_env, n).unwrap_or(n);
        self.names.names.get(&n).unwrap_or_else(|| {
            panic!("Could not find {ix:?} -> {n:?}");
        })
    }
    fn insert(&self, ix: DepNode<'tcx>) -> &Kind {
        self.get(ix)
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
        let mut node = DepNode::new(self.tcx, (def_id, subst));

        if self.tcx.is_closure(def_id) {
            node = DepNode::Type(self.tcx.mk_closure(def_id, subst));
        }

        let name = item_name(self.tcx, def_id, Namespace::TypeNS);
        match self.tcx.def_kind(def_id) {
            DefKind::AssocTy => self.get(node).ident().into(),
            _ => self.get(node).qname_ident(name),
        }
    }

    fn real_ty(&mut self, ty: Ty<'tcx>) -> QName {
        let node = DepNode::Type(ty);
        self.insert(node).ident().into()
    }

    fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let type_id = match self.tcx.def_kind(def_id) {
            DefKind::Closure | DefKind::Struct | DefKind::Enum | DefKind::Union => def_id,
            DefKind::Variant => self.tcx.parent(def_id),
            _ => unreachable!("Not a type or constructor"),
        };
        let mut name = item_name(self.tcx, def_id, Namespace::ValueNS);
        name.capitalize();
        let mut qname = self.ty(type_id, subst);
        qname.name = name.into();
        qname
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
        let node = match util::item_type(tcx, def_id) {
            ItemType::Closure => {
                DepNode::Hacked(HackedId::Accessor(ix.as_u32() as u8), def_id, subst)
            }
            _ => DepNode::new(tcx, (def_id, subst)),
        };

        let clone = self.get(node);
        match util::item_type(tcx, def_id) {
            ItemType::Closure => clone.ident().into(),
            ItemType::Type => {
                let variant_def = &tcx.adt_def(def_id).variants()[variant.into()];
                let variant = variant_def;
                let name: Ident = format!(
                    "{}_{}",
                    variant.name.as_str().to_ascii_lowercase(),
                    variant.fields[ix].name
                )
                .into();
                clone.qname_ident(name.into())
            }
            _ => panic!("accessor: invalid item kind"),
        }
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

    fn import_prelude_module(&mut self, _: PreludeModule) {
        ()
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

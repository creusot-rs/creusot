use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::{AttrArgs, def_id::DefId};
use rustc_middle::{
    thir,
    ty::{self, EarlyBinder, GenericArgs, GenericArgsRef, TypingEnv},
};
use rustc_span::Symbol;

use crate::{
    backend::dependency::Dependency,
    contracts_items::creusot_clause_attrs,
    ctx::{RevealModifier, TranslationCtx},
    translation::specification::SpecAttrError::{InvalidTerm, InvalidTokens},
};

struct ScopeItemVisitor<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    thir: &'a thir::Thir<'tcx>,
    typing_env: TypingEnv<'tcx>,

    out: &'a mut FxHashMap<Dependency<'tcx>, Symbol>,
    sym: Symbol,
    fixup: &'a (dyn 'a + Fn(GenericArgsRef<'tcx>) -> GenericArgsRef<'tcx>),
}

impl<'a, 'tcx> thir::visit::Visitor<'a, 'tcx> for ScopeItemVisitor<'a, 'tcx> {
    fn thir(&self) -> &'a thir::Thir<'tcx> {
        self.thir
    }

    fn visit_stmt(&mut self, stmt: &'a thir::Stmt<'tcx>) {
        if let thir::StmtKind::Let { initializer: Some(init), .. } = &stmt.kind {
            for arg in self.thir[*init].ty.walk() {
                if let ty::GenericArgKind::Type(ty) = arg.kind()
                    && let ty::FnDef(mut did, args) = *ty.kind()
                {
                    let fix = self.fixup;
                    let mut reveal_args = fix(args.skip_binder());
                    match ty::Instance::try_resolve(self.ctx.tcx, self.typing_env, did, reveal_args)
                    {
                        Ok(Some(inst)) => {
                            did = inst.def_id();
                            reveal_args = inst.args;
                        }
                        _ => {}
                    }

                    self.out.insert(Dependency::Item(did, reveal_args), self.sym);
                }
            }
        }
        thir::visit::walk_stmt(self, stmt)
    }
}

impl<'tcx> TranslationCtx<'tcx> {
    fn collect_scope_items_recursive(
        &self,
        out: &mut FxHashMap<Dependency<'tcx>, Symbol>,
        source: DefId,
        typing_env: TypingEnv<'tcx>,
        clause: &str,
        filter: &dyn Fn(Symbol) -> bool,
    ) {
        // recurse first so we override parent
        match self.def_key(source).parent {
            Some(parent) => self.collect_scope_items_recursive(
                out,
                DefId { index: parent, krate: source.krate },
                typing_env,
                clause,
                filter,
            ),
            None => {}
        }

        let get_creusot_item = |arg: &AttrArgs| {
            let predicate_name = match arg {
                AttrArgs::Eq { expr: l, .. } => l.symbol,
                _ => return Err(InvalidTokens { id: source }),
            };
            if filter(predicate_name) {
                Ok(Some((
                    self.creusot_item(predicate_name).ok_or(InvalidTerm { id: source })?,
                    predicate_name,
                )))
            } else {
                Ok(None)
            }
        };
        for attr in creusot_clause_attrs(self.tcx, source, clause).map(get_creusot_item) {
            if let Ok(Some((def, sym))) = attr {
                let def = def.expect_local();
                let def_generics = GenericArgs::identity_for_item(self.tcx, def);
                let source_generics = GenericArgs::identity_for_item(self.tcx, source);
                let fix = |args: GenericArgsRef<'tcx>| {
                    // add potentially missing lifetime generics
                    // for example, this can happen when we expand
                    //
                    // #[conceal(..)]
                    // impl<T> Trait<'_> for T {}
                    //
                    // into
                    // // we couldn't keep the early bound lifetime used in the trait
                    // fn companion<T>(_: PhantomData<T>) { .. }
                    if def_generics.len() < source_generics.len() {
                        let subst = self.mk_args(
                            &source_generics[source_generics.len() - def_generics.len()..],
                        );
                        self.instantiate_and_normalize_erasing_regions(
                            subst,
                            self.typing_env(source),
                            EarlyBinder::bind(self.tcx, args),
                        )
                    } else {
                        args
                    }
                };

                let (thir, body) = self.thir_body(def);
                let thir = &*thir.borrow();
                thir::visit::walk_expr(
                    &mut ScopeItemVisitor { ctx: self, thir, typing_env, out, sym, fixup: &fix },
                    &thir[body],
                );
            }
        }
    }

    fn collect_scope_items(
        &self,
        source: DefId,
        clause: &str,
        filter: impl Fn(Symbol) -> bool,
    ) -> FxHashMap<Dependency<'tcx>, Symbol> {
        let mut out = FxHashMap::default();
        self.collect_scope_items_recursive(
            &mut out,
            source,
            self.typing_env(source),
            clause,
            &filter,
        );
        out
    }

    pub(crate) fn collect_conceal_reveal_items(
        &self,
        source: DefId,
    ) -> FxHashMap<Dependency<'tcx>, RevealModifier> {
        self.collect_scope_items(source, "vis_modifier", |sym| {
            let sym = sym.as_str();
            sym.starts_with("conceal_") || sym.starts_with("reveal_")
        })
        .into_iter()
        .map(|(dep, sym)| {
            (
                dep,
                if sym.as_str().starts_with("conceal_") {
                    RevealModifier::Conceal
                } else if sym.as_str().starts_with("reveal") {
                    RevealModifier::Reveal
                } else {
                    unreachable!()
                },
            )
        })
        .collect()
    }

    pub(crate) fn collect_import_items(&self, source: DefId) -> FxHashSet<Dependency<'tcx>> {
        self.collect_scope_items(source, "import", |sym| {
            let sym = sym.as_str();
            sym.starts_with("import_")
        })
        .into_iter()
        .map(|(dep, _)| dep)
        .collect()
    }
}

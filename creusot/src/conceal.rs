use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{
    AttrArgs,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    thir,
    ty::{self, EarlyBinder, GenericArgs, GenericArgsRef, TypingEnv},
};

use crate::{
    backend::dependency::Dependency,
    contracts_items::creusot_clause_attrs,
    ctx::{RevealModifier, TranslationCtx},
    translation::specification::SpecAttrError::{InvalidTerm, InvalidTokens},
};

impl<'tcx> TranslationCtx<'tcx> {
    fn compute_reveal_modifiers_recursive(
        &self,
        out: &mut FxHashMap<Dependency<'tcx>, RevealModifier>,
        source: DefId,
        typing_env: TypingEnv<'tcx>,
    ) {
        // recurse first so we override parent
        match self.def_key(source).parent {
            Some(parent) => self.compute_reveal_modifiers_recursive(
                out,
                DefId { index: parent, krate: source.krate },
                typing_env,
            ),
            None => {}
        }

        let get_creusot_item = |arg: &AttrArgs| {
            let predicate_name = match arg {
                AttrArgs::Eq { expr: l, .. } => l.symbol,
                _ => return Err(InvalidTokens { id: source }),
            };
            Ok((
                self.creusot_item(predicate_name).ok_or(InvalidTerm { id: source })?,
                predicate_name.as_str().starts_with("reveal"),
            ))
        };
        for attr in creusot_clause_attrs(self.tcx, source, "reveal").map(get_creusot_item) {
            if let Ok((def, reveal)) = attr {
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

                let (thir, mut body) = self.thir_body(def);
                let thir = &*thir.borrow();
                loop {
                    match &thir[body].kind {
                        thir::ExprKind::Scope { value, .. } => body = *value,
                        thir::ExprKind::Block { block } => {
                            let block = &thir[*block];
                            for &stmt in &block.stmts {
                                let stmt = &thir[stmt];
                                if let thir::StmtKind::Let { initializer: Some(init), .. } =
                                    &stmt.kind
                                {
                                    let ty = &thir[*init].ty;
                                    if let ty::FnDef(mut reveal_def, reveal_args) = *ty.kind() {
                                        let mut reveal_args = fix(reveal_args.skip_binder());
                                        match ty::Instance::try_resolve(
                                            self.tcx,
                                            typing_env,
                                            reveal_def,
                                            reveal_args,
                                        ) {
                                            Ok(Some(inst)) => {
                                                reveal_def = inst.def_id();
                                                reveal_args = inst.args;
                                            }
                                            _ => {}
                                        }

                                        out.insert(
                                            Dependency::Item(reveal_def, reveal_args),
                                            if reveal {
                                                RevealModifier::Reveal
                                            } else {
                                                RevealModifier::Conceal
                                            },
                                        );
                                    }
                                }
                            }

                            if let Some(expr) = block.expr {
                                body = expr;
                            } else {
                                break;
                            }
                        }
                        _ => break,
                    }
                }
            }
        }
    }

    pub(crate) fn compute_reveal_modifiers(
        &self,
        source: DefId,
    ) -> FxHashMap<Dependency<'tcx>, RevealModifier> {
        let mut out = FxHashMap::default();
        self.compute_reveal_modifiers_recursive(&mut out, source, self.typing_env(source));
        out
    }
}

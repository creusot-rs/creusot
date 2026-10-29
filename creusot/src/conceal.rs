use rustc_hir::{
    AttrArgs,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    thir,
    ty::{self, EarlyBinder, GenericArgs, GenericArgsRef},
};

use crate::{
    contracts_items::creusot_clause_attrs,
    ctx::TranslationCtx,
    translation::specification::SpecAttrError::{InvalidTerm, InvalidTokens},
};

impl<'tcx> TranslationCtx<'tcx> {
    pub(crate) fn revealed_from(
        &self,
        source: LocalDefId,
        item: DefId,
        item_args: GenericArgsRef<'tcx>,
    ) -> bool {
        let key = self.def_key(source);
        match key.parent {
            Some(parent) => {
                let mut vis =
                    self.revealed_from(LocalDefId { local_def_index: parent }, item, item_args);

                let get_creusot_item = |arg: &AttrArgs| {
                    let predicate_name = match arg {
                        AttrArgs::Eq { expr: l, .. } => l.symbol,
                        _ => return Err(InvalidTokens { id: source.to_def_id() }),
                    };
                    Ok((
                        self.creusot_item(predicate_name)
                            .ok_or(InvalidTerm { id: source.to_def_id() })?,
                        predicate_name.as_str().starts_with("reveal"),
                    ))
                };
                for attr in creusot_clause_attrs(self.tcx, source.to_def_id(), "reveal")
                    .map(get_creusot_item)
                {
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
                                    self.typing_env(source.to_def_id()),
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
                                        if let thir::StmtKind::Let {
                                            initializer: Some(init), ..
                                        } = &stmt.kind
                                        {
                                            let ty = &thir[*init].ty;
                                            if let ty::FnDef(reveal_def, reveal_args) = *ty.kind() {
                                                let reveal_args = fix(reveal_args.skip_binder());

                                                if reveal_def == item && reveal_args == item_args {
                                                    vis = reveal;
                                                }
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

                vis
            }
            None => true,
        }
    }
}

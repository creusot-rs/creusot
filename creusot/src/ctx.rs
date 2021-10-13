use indexmap::{IndexMap, IndexSet};
use rustc_data_structures::captures::Captures;
use rustc_errors::DiagnosticId;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::definitions::DefPathData;
use rustc_index::vec::Idx;
use rustc_middle::ty::Visibility;
use rustc_middle::ty::{AssocItemContainer, TyCtxt};
use rustc_resolve::Namespace;
use rustc_session::Session;
use rustc_span::Span;
pub use util::ItemType;
use why3::declaration::{Module, TyDecl};
use why3::QName;

pub use crate::clone_map::*;
use crate::translation::external::{self, CrateMetadata};
use crate::translation::interface::interface_for;
use crate::util::item_type;
use crate::{options::Options, util};

enum TranslatedItem<'tcx> {
    Hybrid { interface: Module, modl: Module, proof_modl: Module, dependencies: CloneSummary<'tcx> },
    Logic { interface: Module, modl: Module, dependencies: CloneSummary<'tcx> },
    Program { interface: Module, modl: Module, dependencies: CloneSummary<'tcx> },
    Trait { modl: Module, dependencies: CloneSummary<'tcx> },
    Impl { interface: Module, modl: Module, dependencies: CloneSummary<'tcx> },
    Extern { interface: Module, body: DefaultOrExtern<'tcx> },
}

enum DefaultOrExtern<'tcx> {
    // dependencies is always empty.
    Default { modl: Module, dependencies: CloneSummary<'tcx> },
    Extern(DefId),
}

impl TranslatedItem<'tcx> {
    pub fn dependencies(&'a self, metadata: &'a CrateMetadata<'tcx>) -> &'a CloneSummary<'tcx> {
        use TranslatedItem::*;
        match self {
            Hybrid { dependencies, .. } => dependencies,
            Logic { dependencies, .. } => dependencies,
            Program { dependencies, .. } => dependencies,
            Trait { dependencies, .. } => dependencies,
            Impl { dependencies, .. } => dependencies,
            Extern { body, .. } => match body {
                DefaultOrExtern::Default { dependencies, .. } => dependencies,
                DefaultOrExtern::Extern(def_id) => metadata.dependencies(*def_id).unwrap(),
            },
        }
    }

    pub fn body(&'a self, metadata: &'a CrateMetadata<'tcx>) -> &'a Module {
        use TranslatedItem::*;
        match self {
            Hybrid { modl, .. } => modl,
            Logic { modl, .. } => modl,
            Program { modl, .. } => modl,
            Trait { modl, .. } => modl,
            Impl { modl, .. } => modl,
            Extern { body, .. } => match body {
                DefaultOrExtern::Default { modl, .. } => modl,
                DefaultOrExtern::Extern(def_id) => metadata.body(*def_id).unwrap(),
            },
        }
    }

    pub fn modules(
        &'a self,
        metadata: &'a CrateMetadata<'tcx>,
    ) -> Box<dyn Iterator<Item = &Module> + 'a> {
        use std::iter;
        use TranslatedItem::*;
        match self {
            Hybrid { interface, proof_modl, modl, .. } => {
                box iter::once(interface).chain(iter::once(modl)).chain(iter::once(proof_modl))
            }
            Logic { interface, modl, .. } => box iter::once(interface).chain(iter::once(modl)),
            Program { interface, modl, .. } => box iter::once(interface).chain(iter::once(modl)),
            Trait { modl, .. } => box iter::once(modl),
            Impl { modl, interface, .. } => box iter::once(interface).chain(iter::once(modl)),
            Extern { interface, body, .. } => match body {
                DefaultOrExtern::Default { modl, .. } => {
                    box iter::once(interface).chain(iter::once(modl))
                }
                DefaultOrExtern::Extern(def_id) => {
                    box iter::once(interface).chain(iter::once(metadata.body(*def_id).unwrap()))
                }
            },
        }
    }
}

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'sess, 'tcx> {
    pub sess: &'sess Session,
    pub tcx: TyCtxt<'tcx>,
    pub translated_items: IndexSet<DefId>,
    pub types: Vec<TyDecl>,
    functions: IndexMap<DefId, TranslatedItem<'tcx>>,
    pub externs: CrateMetadata<'tcx>,
    pub opts: &'sess Options,
}

impl<'tcx, 'sess> TranslationCtx<'sess, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'sess Session, opts: &'sess Options) -> Self {
        Self {
            sess,
            tcx,
            translated_items: IndexSet::new(),
            types: Vec::new(),
            functions: IndexMap::new(),
            externs: CrateMetadata::new(tcx),
            opts,
        }
    }

    pub fn load_metadata(&mut self) {
        self.externs.load(&self.opts.extern_paths);
    }

    pub fn translate(&mut self, def_id: DefId) {
        debug!("translating {:?}", def_id);
        match item_type(self.tcx, def_id) {
            ItemType::Trait => self.translate_trait(def_id),
            ItemType::Impl => self.translate_impl(def_id),
            ItemType::Logic | ItemType::Predicate | ItemType::Program | ItemType::Pure => {
                self.translate_function(def_id)
            }
            ItemType::Type => unreachable!(),
            ItemType::Interface => unreachable!(),
        }
    }

    // Generic entry point for function translation
    pub fn translate_function(&mut self, def_id: DefId) {
        if let Some(assoc) = self.tcx.opt_associated_item(def_id) {
            match assoc.container {
                AssocItemContainer::TraitContainer(id) => self.translate(id),
                AssocItemContainer::ImplContainer(id) => {
                    if let Some(_) = self.tcx.trait_id_of_impl(id) {
                        self.translate(id)
                    }
                }
            }
        }

        if !self.translated_items.insert(def_id) {
            return;
        }

        if let Some(local_id) = def_id.as_local() {
            let hir_id = self.tcx.hir().local_def_id_to_hir_id(local_id);
            if !self.tcx.hir().maybe_body_owned_by(hir_id).is_some() {
                return;
            }
        }

        if !crate::util::should_translate(self.tcx, def_id) {
            info!("Skipping {:?}", def_id);
            return;
        }

        let span = self.tcx.hir().span_if_local(def_id).unwrap_or(rustc_span::DUMMY_SP);
        let (interface, deps) = interface_for(self, def_id);

        let translated = if !def_id.is_local() {
            debug!("translating {:?} as extern", def_id);
            match self.externs.body(def_id) {
                Some(_) => {
                    TranslatedItem::Extern { interface, body: DefaultOrExtern::Extern(def_id) }
                }
                None => {
                    let default = external::default_decl(self, def_id, span);

                    TranslatedItem::Extern {
                        interface,
                        body: DefaultOrExtern::Default {
                            modl: default,
                            dependencies: CloneSummary::new(),
                        },
                    }
                }
            }
        } else if util::is_logic(self.tcx, def_id) {
            debug!("translating {:?} as logic", def_id);
            let (modl, deps) = crate::translation::translate_logic(self, def_id, span);
            TranslatedItem::Logic { interface, modl, dependencies: deps.summary() }
        } else if util::is_predicate(self.tcx, def_id) {
            debug!("translating {:?} as predicate", def_id);
            let (modl, deps) = crate::translation::translate_predicate(self, def_id, span);
            TranslatedItem::Logic { interface, modl, dependencies: deps.summary() }
        } else if util::is_pure(self.tcx, def_id) {
            debug!("translating {:?} as pure", def_id);
            let (modl, proof_modl, deps) = crate::translation::translate_pure(self, def_id, span);
            TranslatedItem::Hybrid {
                interface,
                modl: modl,
                proof_modl: proof_modl,
                dependencies: deps.summary(),
            }
        } else {
            let kind = self.tcx.def_kind(def_id);
            if kind == DefKind::Fn || kind == DefKind::Closure || kind == DefKind::AssocFn {
                let is_spec = util::is_invariant(self.tcx, def_id);
                if is_spec {
                    return;
                }

                let modl = crate::translation::translate_function(self.tcx, self, def_id);
                TranslatedItem::Program { interface, modl, dependencies: deps.summary() }
            } else {
                unimplemented!("{:?} {:?}", def_id, self.tcx.def_kind(def_id))
            }
        };

        self.functions.insert(def_id, translated);
    }

    pub fn crash_and_error(&self, span: Span, msg: &str) -> ! {
        self.sess.span_fatal_with_code(span, msg, DiagnosticId::Error(String::from("creusot")))
    }

    pub fn warn(&self, span: Span, msg: &str) {
        self.sess.span_warn_with_code(
            span,
            msg,
            DiagnosticId::Lint {
                name: String::from("creusot"),
                has_future_breakage: false,
                is_force_warn: true,
            },
        )
    }

    pub fn add_type(&mut self, decl: TyDecl) {
        let mut dependencies = decl.used_types();
        let mut pos = 0;
        while !dependencies.is_empty() && pos < self.types.len() {
            dependencies.remove(&self.types[pos].ty_name);
            pos += 1;
        }

        self.types.insert(pos, decl);
    }

    pub fn add_trait(&mut self, def_id: DefId, trait_decl: Module) {
        self.functions.insert(
            def_id,
            TranslatedItem::Trait { modl: trait_decl, dependencies: CloneSummary::new() },
        );
    }

    pub fn add_impl(
        &mut self,
        def_id: DefId,
        modl: Module,
        interface: Module,
        summary: CloneSummary<'tcx>,
    ) {
        self.functions
            .insert(def_id, TranslatedItem::Impl { interface, modl, dependencies: summary });
    }

    pub fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        self.functions.get(&def_id).map(|f| f.dependencies(&self.externs))
    }

    pub fn should_export(&self) -> bool {
        self.opts.export_metadata
    }

    pub fn should_compile(&self) -> bool {
        !self.opts.dependency
    }

    pub fn modules(&self) -> impl Iterator<Item = &Module> + Captures<'tcx> {
        self.functions.values().flat_map(|m| m.modules(&self.externs))
    }
}

pub fn logic_declaration_metadata<'a>(
    ctx: &'a TranslationCtx<'_, '_>,
) -> external::LogicMetadata<'a> {
    ctx.functions
        .iter()
        .filter(|(def_id, _)| {
            ctx.tcx.visibility(**def_id) == Visibility::Public && def_id.is_local()
        })
        .map(|(def_id, func)| (def_id.expect_local().index(), func.body(&ctx.externs)))
        .collect()
}

pub fn clone_metadata(ctx: &TranslationCtx<'_, 'tcx>) -> external::CloneMetaSerialize<'tcx> {
    ctx.functions
        .iter()
        .filter(|(def_id, _)| {
            ctx.tcx.visibility(**def_id) == Visibility::Public && def_id.is_local()
        })
        .map(|(def_id, v)| (*def_id, v.dependencies(&ctx.externs).clone().into_iter().collect()))
        .collect()
}

use heck::CamelCase;

pub fn translate_type_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, true)
}

pub fn translate_value_id(tcx: TyCtxt, def_id: DefId) -> QName {
    translate_defid(tcx, def_id, false)
}

fn translate_defid(tcx: TyCtxt, def_id: DefId, ty: bool) -> QName {
    let def_path = tcx.def_path(def_id);

    let mut segments = Vec::new();

    let mut crate_name = tcx.crate_name(def_id.krate).to_string().to_camel_case();
    if crate_name.chars().next().unwrap().is_numeric() {
        crate_name = format!("C{}", crate_name);
    }

    segments.push(crate_name);

    for seg in def_path.data[..].iter() {
        match seg.data {
            // DefPathData::CrateRoot => segments.push(tcx.crate_name(def_id.krate).to_string()),
            // CORE ASSUMPTION: Once we stop seeing TypeNs we never see it again.
            DefPathData::Ctor => {}
            _ => segments.push(format!("{}", seg).to_camel_case()),
        }
    }

    let kind = tcx.def_kind(def_id);
    use rustc_hir::def::DefKind::*;

    let name;
    match (kind, kind.ns()) {
        (_, _) if ty => {
            name = segments.into_iter().map(|seg| seg.to_lowercase()).collect();
            segments = vec!["Type".to_owned()];
        }
        (Ctor(_, _) | Variant | Struct | Enum, _) => {
            segments[0] = segments[0].to_camel_case();
            name = segments;
            segments = vec!["Type".to_owned()];
        }
        (Trait | Mod | Impl, _) => {
            name = segments;
            segments = Vec::new();
        }
        (_, Some(Namespace::ValueNS)) | (Closure, _) => {
            name = vec![(&*util::method_name(tcx, def_id)).into()];
        }
        (a, b) => unreachable!("{:?} {:?} {:?}", a, b, segments),
    }
    let module = if segments.is_empty() { Vec::new() } else { vec![segments.join("_").into()] };

    QName { module, name: name.join("_").into() }
}

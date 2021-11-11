pub use crate::clone_map::*;
use crate::creusot_items::{self, CreusotItems};
use crate::metadata::{BinaryMetadata, Metadata};
use crate::translation::interface::interface_for;
use crate::translation::specification::typing::Term;
use crate::translation::ty;
use crate::translation::{external, specification};
use crate::util::item_type;
use crate::{options::Options, util};
use indexmap::{IndexMap, IndexSet};
use rustc_data_structures::captures::Captures;
use rustc_errors::DiagnosticId;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{AssocItemContainer, TyCtxt};
use rustc_session::Session;
use rustc_span::Span;
use rustc_span::Symbol;
pub use util::{item_name, module_name, ItemType};
use why3::declaration::{Decl, Module, TyDecl};

pub enum TranslatedItem<'tcx> {
    Logic {
        interface: Module,
        modl: Module,
        proof_modl: Option<Module>,
        dependencies: CloneSummary<'tcx>,
        has_axioms: bool,
    },
    Program {
        interface: Module,
        modl: Module,
        dependencies: CloneSummary<'tcx>,
    },
    Trait {
        has_axioms: bool,
        dependencies: CloneSummary<'tcx>, // always empty
    },
    Impl {
        modl: Module, // Refinement of traits,
        dependencies: CloneSummary<'tcx>,
    },
    AssocTy {
        modl: Module,
        dependencies: CloneSummary<'tcx>,
    },
    Extern {
        interface: Module,
        body: Module,
        dependencies: Result<CloneSummary<'tcx>, DefId>,
    },
}

pub struct TypeDeclaration {
    pub ty_decl: TyDecl,
    pub accessors: IndexMap<DefId, IndexMap<DefId, Vec<Decl>>>,
}

impl TypeDeclaration {
    pub fn accessors(&self) -> impl Iterator<Item = &Decl> {
        self.accessors.values().flat_map(|v| v.values().flat_map(|f| f.iter()))
    }
}

pub enum DefaultOrExtern<'tcx> {
    // dependencies is always empty.
    Default { modl: Module, dependencies: CloneSummary<'tcx> },
    Extern { modl: Module, def_id: DefId },
}

impl TranslatedItem<'tcx> {
    pub fn dependencies(&'a self, metadata: &'a Metadata<'tcx>) -> &'a CloneSummary<'tcx> {
        use TranslatedItem::*;
        match self {
            Extern { dependencies, .. } => match dependencies {
                Ok(deps) => deps,
                Err(id) => metadata.dependencies(*id).unwrap(),
            },
            _ => self.local_dependencies(),
        }
    }

    // Get the dependencies of a locally defined function
    // Panics if `self` is not local
    pub fn local_dependencies(&self) -> &CloneSummary<'tcx> {
        use TranslatedItem::*;

        match self {
            Logic { dependencies, .. } => dependencies,
            Program { dependencies, .. } => dependencies,
            Trait { dependencies, .. } => dependencies,
            Impl { dependencies, .. } => dependencies,
            AssocTy { dependencies, .. } => dependencies,
            Extern { .. } => unreachable!("local_dependencies: called on a non-local item"),
        }
    }

    pub fn has_axioms(&self) -> bool {
        match self {
            TranslatedItem::Trait { has_axioms, .. } => *has_axioms,
            TranslatedItem::Logic { has_axioms, .. } => *has_axioms,
            _ => false,
        }
    }

    pub fn modules(&'a self) -> Box<dyn Iterator<Item = &Module> + 'a> {
        use std::iter;
        use TranslatedItem::*;
        match self {
            Logic { interface, modl, proof_modl, .. } => {
                box iter::once(interface).chain(iter::once(modl)).chain(proof_modl.iter())
            }
            Program { interface, modl, .. } => box iter::once(interface).chain(iter::once(modl)),
            Trait { .. } => box iter::empty(),
            Impl { modl, .. } => box iter::once(modl),
            AssocTy { modl, .. } => box iter::once(modl),
            Extern { interface, body, .. } => box iter::once(interface).chain(iter::once(body)),
        }
    }
}

// TODO: The state in here should be as opaque as possible...
pub struct TranslationCtx<'sess, 'tcx> {
    pub sess: &'sess Session,
    pub tcx: TyCtxt<'tcx>,
    pub translated_items: IndexSet<DefId>,
    pub types: IndexMap<DefId, TypeDeclaration>,
    functions: IndexMap<DefId, TranslatedItem<'tcx>>,
    terms: IndexMap<DefId, Term<'tcx>>,
    pub externs: Metadata<'tcx>,
    pub opts: &'sess Options,
    creusot_items: CreusotItems,
}

impl<'tcx, 'sess> TranslationCtx<'sess, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, sess: &'sess Session, opts: &'sess Options) -> Self {
        let creusot_items = creusot_items::local_creusot_items(tcx);
        Self {
            sess,
            tcx,
            translated_items: IndexSet::new(),
            types: Default::default(),
            functions: IndexMap::new(),
            externs: Metadata::new(tcx),
            terms: Default::default(),
            creusot_items,
            opts,
        }
    }

    pub fn load_metadata(&mut self) {
        self.externs.load(&self.opts.extern_paths);
    }

    pub fn translate(&mut self, def_id: DefId) {
        debug!("translating {:?}", def_id);
        if self.translated_items.contains(&def_id) {
            return;
        }
        match item_type(self.tcx, def_id) {
            ItemType::Trait => self.translate_trait(def_id),
            ItemType::Impl => self.translate_impl(def_id),
            ItemType::Logic | ItemType::Predicate | ItemType::Program => {
                self.translate_function(def_id)
            }
            ItemType::AssocTy => {
                let (modl, dependencies) = self.translate_assoc_ty(def_id);
                self.translated_items.insert(def_id);
                self.functions.insert(def_id, TranslatedItem::AssocTy { modl, dependencies });
            }
            ItemType::Type => unreachable!("ty"),
            ItemType::Interface => unreachable!(),
        }
    }

    // Generic entry point for function translation
    pub fn translate_function(&mut self, def_id: DefId) {
        assert!(matches!(
            self.tcx.def_kind(def_id),
            DefKind::Fn | DefKind::Closure | DefKind::AssocFn
        ));

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

        if !crate::util::should_translate(self.tcx, def_id) {
            info!("Skipping {:?}", def_id);
            return;
        }

        let span = self.tcx.hir().span_if_local(def_id).unwrap_or(rustc_span::DUMMY_SP);
        let (interface, deps) = interface_for(self, def_id);

        let translated = if util::is_logic(self.tcx, def_id) {
            debug!("translating {:?} as logic", def_id);
            let (modl, proof_modl, has_axioms, deps) =
                crate::translation::translate_logic_or_predicate(self, def_id, span);
            TranslatedItem::Logic {
                interface,
                modl,
                proof_modl,
                has_axioms,
                dependencies: deps.summary(),
            }
        } else if util::is_predicate(self.tcx, def_id) {
            debug!("translating {:?} as predicate", def_id);
            let (modl, proof_modl, has_axioms, deps) =
                crate::translation::translate_logic_or_predicate(self, def_id, span);
            TranslatedItem::Logic {
                interface,
                modl,
                proof_modl,
                has_axioms,
                dependencies: deps.summary(),
            }
        } else if !def_id.is_local() {
            debug!("translating {:?} as extern", def_id);

            let ext_modl = external::extern_module(self, def_id);

            TranslatedItem::Extern { interface, body: ext_modl.0, dependencies: ext_modl.1 }
        } else {
            if util::is_spec(self.tcx, def_id) {
                return;
            }

            let modl = crate::translation::translate_function(self, def_id);
            TranslatedItem::Program { interface, modl, dependencies: deps.summary() }
        };

        self.functions.insert(def_id, translated);
    }

    pub fn translate_accessor(&mut self, field_id: DefId) {
        use rustc_middle::ty::DefIdTree;

        if !self.translated_items.insert(field_id) {
            return;
        }

        let parent = self.tcx.parent(field_id).unwrap();
        let (adt_did, variant_did) = match self.tcx.def_kind(parent) {
            DefKind::Variant => (self.tcx.parent(parent).unwrap(), parent),
            DefKind::Struct | DefKind::Enum | DefKind::Union => {
                (parent, self.tcx.adt_def(parent).variants[0u32.into()].def_id)
            }
            _ => unreachable!(),
        };

        let accessor = ty::translate_accessor(self, adt_did, variant_did, field_id);

        self.types[&adt_did].accessors.entry(variant_did).or_default().insert(field_id, accessor);
    }

    pub fn term(&mut self, def_id: DefId) -> Option<&Term<'tcx>> {
        if !def_id.is_local() {
            return self.externs.term(def_id);
        }

        if util::has_body(self, def_id) {
            let t = self.terms.entry(def_id).or_insert_with(|| {
                specification::typing::typecheck(self.tcx, def_id.expect_local())
            });
            Some(t)
        } else {
            None
        }
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

    pub fn add_type(&mut self, def_id: DefId, decl: TyDecl) {
        self.types.insert(def_id, TypeDeclaration { ty_decl: decl, accessors: Default::default() });
        // self.types.insert(pos, decl);
    }

    pub fn add_trait(&mut self, def_id: DefId, has_axioms: bool) {
        self.functions.insert(
            def_id,
            TranslatedItem::Trait { has_axioms, dependencies: CloneSummary::new() },
        );
    }

    pub fn add_impl(&mut self, def_id: DefId, modl: Module) {
        self.functions
            .insert(def_id, TranslatedItem::Impl { modl, dependencies: CloneSummary::new() });
    }

    pub fn dependencies(&self, def_id: DefId) -> Option<&CloneSummary<'tcx>> {
        self.item(def_id).map(|f| f.dependencies(&self.externs))
    }

    pub fn item(&self, def_id: DefId) -> Option<&TranslatedItem<'tcx>> {
        self.functions.get(&def_id)
    }

    pub fn should_export(&self) -> bool {
        self.opts.export_metadata
    }

    pub fn should_compile(&self) -> bool {
        !self.opts.dependency
    }

    pub fn modules(&self) -> impl Iterator<Item = &Module> + Captures<'tcx> {
        self.functions.values().flat_map(|m| m.modules())
    }

    pub fn metadata(&self) -> BinaryMetadata<'tcx> {
        BinaryMetadata::from_parts(self.tcx, &self.functions, &self.terms, &self.creusot_items)
    }

    pub fn creusot_item(&self, name: Symbol) -> Option<DefId> {
        self.creusot_items
            .symbol_to_id
            .get(&name)
            .cloned()
            .or_else(|| self.externs.creusot_item(name))
    }
}

use crate::naming::ModulePath;
use why3::declaration::Module;

/// Module with a path to the file it is defined in.
/// We use this for modular translation (one file per module).
/// In monolithic translation, the path is left empty.
pub struct FileModule {
    pub path: ModulePath,
    pub modl: Module,
}

pub enum TranslatedItem {
    Logic {
        /// Proof obligations emerging from the contract of a logic function
        proof_modl: Option<FileModule>,
    },
    Program {
        /// An ordinary Rust function
        modl: Option<FileModule>,
    },
    Impl {
        /// Trait refinement obligations
        modls: Vec<FileModule>,
    },
}

impl<'a> TranslatedItem {
    pub(crate) fn modules(self) -> Box<dyn Iterator<Item = FileModule>> {
        use TranslatedItem::*;
        match self {
            Logic { proof_modl } => Box::new(proof_modl.into_iter()),
            Program { modl } => Box::new(modl.into_iter()),
            Impl { modls } => Box::new(modls.into_iter()),
        }
    }
}

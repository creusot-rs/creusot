use why3::declaration::Module;

pub enum TranslatedItem {
    Logic {
        /// Proof obligations emerging from the contract of a logic function
        proof_modl: Option<Module>,
    },
    Program {
        /// An ordinary Rust function
        modl: Option<Module>,
    },
    Impl {
        /// Trait refinement obligations
        modls: Vec<Module>,
    },
}

impl<'a> TranslatedItem {
    pub(crate) fn modules(self) -> Box<dyn Iterator<Item = Module>> {
        use TranslatedItem::*;
        match self {
            Logic { proof_modl } => Box::new(proof_modl.into_iter()),
            Program { modl } => Box::new(modl.into_iter()),
            Impl { modls } => Box::new(modls.into_iter()),
        }
    }
}

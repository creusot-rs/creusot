use why3::declaration::Decl;

use std::collections::HashMap;

#[derive(Debug)]
pub struct ModuleTree {
    decls: Vec<Decl>,
    inner: HashMap<String, ModuleTree>,
}

impl ModuleTree {
    pub fn new() -> Self {
        Self { decls: Vec::new(), inner: HashMap::new() }
    }

    pub fn add_decl(&mut self, key: why3::mlcfg::QName, decl: Decl) {
        let mut node = self;

        for elem in key.module.iter().chain(key.name.iter()) {
            if node.inner.get_mut(elem).is_none() {
                node.inner.insert(elem.clone(), ModuleTree::new());
            }
            node = node.inner.get_mut(elem).unwrap();
        }

        node.decls.push(decl);
    }

    pub fn reify(self) -> Vec<Decl> {
        self.inner.into_iter()
            .map(|(n, c)| c.reify_(n))
            .chain(self.decls.into_iter())
            .collect()
    }

    fn reify_(self, nm: String) -> Decl {
        Decl::Scope(why3::declaration::Scope {
            name: nm,
            decls: self.inner.into_iter()
                .map(|(n, c)| c.reify_(n))
                .chain(self.decls.into_iter())
                .collect::<Vec<_>>()
        })
    }
}

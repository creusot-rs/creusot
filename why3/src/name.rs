use indexmap::Equivalent;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Ident(pub(crate) String);

// TODO: Make this try_from and test for validity
impl From<&str> for Ident {
    fn from(nm: &str) -> Self {
        Ident(nm.to_owned())
    }
}

impl From<String> for Ident {
    fn from(nm: String) -> Self {
        Ident(nm)
    }
}

impl Equivalent<QName> for Ident {
    fn equivalent(&self, key: &QName) -> bool {
        self.0 == key.name
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct QName {
    pub module: Vec<String>,
    pub name: String,
}

impl QName {
    pub fn name(&self) -> String {
        self.name.clone()
    }

    pub fn module_name(mut self) -> QName {
        let name = self.module.pop().unwrap();

        QName { module: self.module, name }
    }

    pub fn from_string(s: &str) -> Option<QName> {
        let mut chunks = s.split('.');

        let name = chunks.next_back()?;
        let module = chunks.map(|s| s.into()).collect();

        Some(QName { module, name: name.into() })
    }
}

impl From<&str> for QName {
    fn from(nm: &str) -> Self {
        QName { module: vec![], name: nm.to_string() }
    }
}

// TODO: deprecate this
impl From<String> for QName {
    fn from(nm: String) -> Self {
        QName { module: vec![], name: nm }
    }
}

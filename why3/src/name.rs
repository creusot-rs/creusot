use std::{borrow::Cow, ops::Deref};

use indexmap::Equivalent;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Ident(pub(crate) String);

impl Ident {
    // Constructs a valid why3 identifier representing a given string
    pub fn build(name: &str) -> Self {
        if RESERVED.contains(&name) {
            return Ident(format!("{}'", name));
        }
        // TODO: ensure that all characters are valid
        Ident(name.into())
    }
}

// TODO: Make this try_from and test for validity
impl From<&str> for Ident {
    fn from(nm: &str) -> Self {
        Ident::build(nm)
    }
}

impl From<String> for Ident {
    fn from(nm: String) -> Self {
        Ident::build(&nm)
    }
}

impl<'a> From<&'a Ident> for Cow<'a, str> {
    fn from(id: &'a Ident) -> Cow<'a, str> {
        (&id.0).into()
    }
}

impl Deref for Ident {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Equivalent<QName> for Ident {
    fn equivalent(&self, key: &QName) -> bool {
        self == &key.name
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct QName {
    pub module: Vec<Ident>,
    pub name: Ident,
}

impl QName {
    pub fn name(&self) -> Ident {
        self.name.clone()
    }

    pub fn module_name(&self) -> Option<&Ident> {
        self.module.last()
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
        QName { module: vec![], name: nm.into() }
    }
}

// TODO: deprecate this
impl From<String> for QName {
    fn from(nm: String) -> Self {
        QName { module: vec![], name: nm.into() }
    }
}

// TODO: deprecate this
impl From<Ident> for QName {
    fn from(nm: Ident) -> Self {
        QName { module: vec![], name: nm }
    }
}

const RESERVED: &[&str] = &[
    "abstract",
    "alias",
    "any",
    "assert",
    "assume",
    "at",
    "axiom",
    "break",
    "by",
    "check",
    "clone",
    "coinductive",
    "constant",
    "continue",
    "diverges",
    "do",
    "else",
    "end",
    "ensures",
    "epsilon",
    "exception",
    "export",
    "false",
    "for",
    "fun",
    "function",
    "ghost",
    "goal",
    "if",
    "import",
    "inductive",
    "invariant",
    "label",
    "lemma",
    "let",
    "match",
    "module",
    "mutable",
    "not",
    "old",
    "predicate",
    "private",
    "raise",
    "reads",
    "rec",
    "requires",
    "returns",
    "scope",
    "true",
    "try",
    "type",
    "use",
    "val",
    "variant",
    "while",
    "with",
    "writes",
];

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reserved_idents_made_valid() {
        assert_eq!(Ident::build("clone").0, "clone'")
    }
}

use std::{borrow::Cow, fmt::Write, ops::Deref};

use indexmap::Equivalent;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

use crate::exp::Exp;

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

    pub fn from_string(mut name: String) -> Self {
        if RESERVED.contains(&&*name) {
            name.write_str("'").unwrap();
        }
        Ident(name)
    }

    pub fn to_string(self) -> String {
        self.0
    }

    pub fn decapitalize(&mut self) {
        self.0[..1].make_ascii_lowercase();
    }

    pub fn capitalize(&mut self) {
        self.0[..1].make_ascii_uppercase();
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

impl From<QName> for Exp {
    fn from(q: QName) -> Self {
        Exp::qvar(q)
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
    pub fn as_ident(&self) -> Option<&Ident> {
        if self.module.is_empty() {
            return Some(&self.name);
        } else {
            None
        }
    }
    pub fn name(&self) -> Ident {
        self.name.clone()
    }

    // ooof this is a bad function
    pub fn module_ident(&self) -> Option<&Ident> {
        self.module.last()
    }

    /// Given `Module.name` replaces `name` with `id`.
    pub fn push_ident(&mut self, id: impl Into<Ident>) {
        let old = std::mem::replace(&mut self.name, id.into());
        self.module.push(old);
    }

    pub fn module_qname(mut self) -> QName {
        assert!(!self.module.is_empty(), "ident has no module {:?}", self);
        let id = self.module.pop().unwrap();
        self.name = id;
        self
    }

    pub fn without_search_path(mut self) -> QName {
        let mut i = 0;
        while i < self.module.len() {
            if self.module[i].starts_with(char::is_lowercase) {
                self.module.remove(i);
            } else {
                i += 1
            }
        }
        self
    }

    pub fn from_string(s: &str) -> QName {
        let mut in_paren = false;
        for (i, c) in s.char_indices().rev() {
            match c {
                ')' => in_paren = true,
                '(' => in_paren = false,
                '.' => {
                    if !in_paren {
                        let name = s[i + 1..].into();
                        let module = s[..i].split('.').map(|s| s.into()).collect();
                        return QName { module, name };
                    }
                }
                _ => (),
            }
        }

        s.into()
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
    "done",
    "else",
    "end",
    "ensures",
    "epsilon",
    "exception",
    "exists",
    "export",
    "false",
    "for",
    "forall",
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
    "meta",
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
    "return",
    "returns",
    "scope",
    "to",
    "true",
    "try",
    "type",
    "use",
    "val",
    "var",
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

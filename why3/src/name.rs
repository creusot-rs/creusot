use std::{borrow::Cow, fmt::Write, ops::Deref, sync::atomic::AtomicU64};

use indexmap::Equivalent;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};

use crate::exp::Exp;

static FRESH_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct IdentString(String);

impl IdentString {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<IdentString> for String {
    fn from(id: IdentString) -> Self {
        id.0
    }
}

impl From<String> for IdentString {
    fn from(mut name: String) -> Self {
        // TODO: ensure that all characters are valid
        if RESERVED.contains(&&*name) {
            name.write_str("'").unwrap();
        }
        IdentString(name)
    }
}

impl From<&str> for IdentString {
    fn from(name: &str) -> Self {
        IdentString::from(name.to_string())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Ident {
    name: IdentString,
    id: u64,
}

impl Ident {
    pub fn fresh(name: impl Into<String>) -> Self {
        Ident {
            name: IdentString::from(name.into()),
            id: FRESH_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        }
    }

    // TODO: remove this
    pub fn as_str(&self) -> &str {
        self.name.as_str()
    }
}

impl From<QName> for Exp {
    fn from(q: QName) -> Self {
        Exp::qvar(q)
    }
}

/*
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
 */

impl Equivalent<QName> for Ident {
    fn equivalent(&self, key: &QName) -> bool {
        key.is_ident(&self.name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct QName {
    pub module: Vec<IdentString>,
    pub name: IdentString,
}

impl QName {
    pub fn is_ident(&self, id: &IdentString) -> bool {
        self.module.is_empty() && &self.name == id
    }

    pub fn as_ident(&self) -> IdentString {
        assert!(self.module.is_empty());
        self.name.clone()
    }

    pub fn without_search_path(mut self) -> QName {
        let mut i = 0;
        while i < self.module.len() {
            if self.module[i].0.starts_with(char::is_lowercase) {
                self.module.remove(i);
            } else {
                i += 1
            }
        }
        self
    }

    pub fn to_string(&self) -> String {
        let mut s = String::new();
        for i in self.module.iter() {
            s.push_str(i.as_str());
            s.push('.');
        }
        s.push_str(self.name.as_str());
        s
    }
}

impl From<&str> for QName {
    fn from(s: &str) -> Self {
        let mut in_paren = false;
        for (i, c) in s.char_indices().rev() {
            match c {
                ')' => in_paren = true,
                '(' => in_paren = false,
                '.' => {
                    if !in_paren {
                        let name = IdentString::from(&s[i + 1..]);
                        let module = s[..i].split('.').map(|s| IdentString::from(s)).collect();
                        return QName { module, name };
                    }
                }
                _ => (),
            }
        }

        QName { module: vec![], name: s.into() }
    }
}

impl From<String> for QName {
    fn from(s: String) -> Self {
        s.as_str().into()
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
        assert_eq!(IdentString::from("clone").0, "clone'")
    }
}

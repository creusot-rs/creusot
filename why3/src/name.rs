use crate::exp::Exp;
use indexmap::Equivalent;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};
use std::{
    borrow::Cow,
    fmt::{Display, Write},
    ops::Deref,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Ident(pub(crate) String);

impl Ident {
    /// Constructs a valid why3 identifier representing a given string
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

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn decapitalize(&mut self) {
        self.0[..1].make_ascii_lowercase();
    }

    pub fn capitalize(&mut self) {
        self.0[..1].make_ascii_uppercase();
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

// TODO: Make this `parse` and test for validity
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
        key.is_ident(self)
    }
}

/// A _qualified_ name. This also contains the module path in which to search for this name.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct QName {
    pub module: Box<[Ident]>,
    pub name: Ident,
}

impl QName {
    pub fn is_ident(&self, id: &Ident) -> bool {
        self.module.is_empty() && &self.name == id
    }

    pub fn as_ident(&self) -> Ident {
        assert!(self.module.is_empty());
        self.name.clone()
    }

    pub fn without_search_path(mut self) -> QName {
        self.module =
            self.module.into_iter().skip_while(|s| s.starts_with(char::is_lowercase)).collect();
        self
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
                        let name = s[i + 1..].into();
                        let module = s[..i].split('.').map(|s| s.into()).collect();
                        return QName { module, name };
                    }
                }
                _ => (),
            }
        }

        QName { module: Box::new([]), name: s.into() }
    }
}

impl From<String> for QName {
    fn from(s: String) -> Self {
        s.as_str().into()
    }
}

impl From<Ident> for QName {
    fn from(name: Ident) -> Self {
        QName { module: Box::new([]), name }
    }
}

/// The why3 keywords
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

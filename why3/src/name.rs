use crate::exp::Exp;
use indexmap::Equivalent;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    fmt::Display,
    sync::{LazyLock, RwLock, atomic::AtomicU64},
};
use string_interner::{DefaultStringInterner, DefaultSymbol};

static FRESH_COUNTER: AtomicU64 = AtomicU64::new(1);
static INTERNER: LazyLock<RwLock<DefaultStringInterner>> =
    LazyLock::new(|| RwLock::new(DefaultStringInterner::new()));

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(pub(crate) DefaultSymbol);

fn symbol_to_string(s: DefaultSymbol) -> String {
    INTERNER.read().unwrap().resolve(s).unwrap().to_string()
}

fn intern(s: &str) -> DefaultSymbol {
    INTERNER.write().unwrap().get_or_intern(s)
}

impl Symbol {
    pub fn to_string(self) -> String {
        symbol_to_string(self.0)
    }

    /// Return a name which is not a Why3 keyword.
    pub fn to_identifier(self) -> Symbol {
        *RESERVED.get(&self).unwrap_or(&self)
    }

    pub fn intern(s: &str) -> Self {
        Symbol(intern(s))
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", INTERNER.read().unwrap().resolve(self.0).unwrap())
    }
}

// Adding these placeholders was less hassle than removing all `derive(Serialize)` from the why3 crate
// and removing their use in `creusot/src/run_why3.rs`.
#[cfg(feature = "serialize")]
impl Serialize for Symbol {
    fn serialize<S: serde::Serializer>(&self, _serializer: S) -> Result<S::Ok, S::Error> {
        todo! {}
    }
}

#[cfg(feature = "serialize")]
impl<'d> Deserialize<'d> for Symbol {
    fn deserialize<D: serde::Deserializer<'d>>(_deserializer: D) -> Result<Self, D::Error> {
        todo! {}
    }
}

impl From<Symbol> for String {
    fn from(id: Symbol) -> Self {
        symbol_to_string(id.0)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Ident {
    pub name: Symbol,
    id: u64, // 0 for "bound" identifiers, >0 for "fresh" identifiers
}

impl Ident {
    /// Every call to `fresh` returns a new unique identifier.
    /// Use this for translating source identifiers and for generated identifiers.
    pub fn fresh(name: impl AsRef<str>) -> Self {
        Ident {
            name: Symbol::intern(name.as_ref()),
            id: FRESH_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        }
    }

    /// All `bound` names from the same string are equal.
    /// Use this for fixed identifiers (result, ret)
    pub fn bound(name: impl AsRef<str>) -> Self {
        Ident { name: Symbol::intern(name.as_ref()), id: 0 }
    }

    pub fn name(&self) -> String {
        self.name.to_string()
    }

    pub fn refresh(&self) -> Self {
        Ident {
            name: self.name,
            id: FRESH_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        }
    }

    pub fn unique_str(&self) -> String {
        format!("{}_{}", self.name.to_string(), self.id)
    }

    pub fn unsafe_id(&self) -> u64 {
        self.id
    }

    pub fn unsafe_raw(name: &str, id: u64) -> Self {
        Ident { name: Symbol::intern(name), id }
    }
}

impl Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.name.to_string())?;
        f.write_str("'")?;
        f.write_str(&self.id.to_string())
    }
}

impl From<Ident> for Symbol {
    fn from(id: Ident) -> Self {
        id.name
    }
}

impl From<QName> for Exp {
    fn from(q: QName) -> Self {
        Exp::qvar(q)
    }
}

impl Equivalent<QName> for Ident {
    fn equivalent(&self, key: &QName) -> bool {
        key.is_ident(&self.name)
    }
}

/// A _qualified_ name. This also contains the module path in which to search for this name.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct QName {
    pub module: Box<[Symbol]>,
    pub name: Symbol,
}

impl QName {
    pub fn is_ident(&self, id: &Symbol) -> bool {
        self.module.is_empty() && &self.name == id
    }

    pub fn as_ident(&self) -> Symbol {
        assert!(self.module.is_empty());
        self.name.clone()
    }

    pub fn without_search_path(mut self) -> QName {
        self.module = self
            .module
            .into_iter()
            .skip_while(|s| s.to_string().starts_with(char::is_lowercase))
            .collect();
        self
    }

    pub fn to_string(&self) -> String {
        let mut s = String::new();
        for i in self.module.iter() {
            s.push_str(&i.to_string());
            s.push('.');
        }
        s.push_str(&self.name.to_string());
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
                        let name = Symbol::intern(&s[i + 1..]);
                        let module = s[..i].split('.').map(|s| Symbol::intern(s)).collect();
                        return QName { module, name };
                    }
                }
                _ => (),
            }
        }
        QName { module: Box::new([]), name: Symbol::intern(s) }
    }
}

impl From<String> for QName {
    fn from(s: String) -> Self {
        s.as_str().into()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Name {
    Local(Ident, Option<Symbol>), // Suffix "'pre" or "'post'return'"
    Global(QName),
}

impl Name {
    pub fn local(ident: Ident) -> Self {
        Name::Local(ident, None)
    }

    pub fn to_qname(self) -> QName {
        match self {
            Name::Local(_, _) => panic!("Cannot convert local name to QName"),
            Name::Global(q) => q,
        }
    }

    pub fn to_ident(self) -> Ident {
        match self {
            Name::Local(i, None) => i,
            Name::Local(_, Some(_)) => unimplemented!(),
            Name::Global(_) => panic!("Cannot convert global name to Ident"),
        }
    }
}

pub(crate) static TRUE: LazyLock<Symbol> = LazyLock::new(|| Symbol::intern("True"));

pub(crate) static FALSE: LazyLock<Symbol> = LazyLock::new(|| Symbol::intern("False"));

// A mapping from Why3 keywords to valid identifiers.
static RESERVED: LazyLock<HashMap<Symbol, Symbol>> = LazyLock::new(|| {
    let mut interner = INTERNER.write().unwrap();
    RESERVED_STR
        .into_iter()
        .map(|s| {
            let s1 = Symbol(interner.get_or_intern(s));
            let s2 = Symbol(interner.get_or_intern(format!("{}'", s)));
            (s1, s2)
        })
        .collect()
});

/// The Why3 keywords
const RESERVED_STR: &[&str] = &[
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

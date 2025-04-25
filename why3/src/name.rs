use crate::exp::Exp;
#[cfg(feature = "serialize")]
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    sync::{LazyLock, RwLock, atomic::AtomicU64},
};
use string_interner::{DefaultStringInterner, DefaultSymbol};

static FRESH_COUNTER: AtomicU64 = AtomicU64::new(1);

/// Every call returns a unique `u64` which is `>= 1`.
fn fresh_u64() -> u64 {
    FRESH_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

static INTERNER: LazyLock<RwLock<DefaultStringInterner>> =
    LazyLock::new(|| RwLock::new(DefaultStringInterner::new()));

/// Interned string
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(pub(crate) DefaultSymbol);

fn symbol_to_string(s: DefaultSymbol) -> String {
    INTERNER.read().unwrap().resolve(s).unwrap().to_string()
}

fn intern(s: &str) -> DefaultSymbol {
    INTERNER.write().unwrap().get_or_intern(s)
}

static EMPTY: LazyLock<Symbol> = LazyLock::new(|| Symbol(intern("")));

impl Symbol {
    /// Return the string that this symbol represents.
    ///
    /// Is there a way to safely get a `&str` from a `Symbol`?
    /// The problem is that the `INTERNER` is behind a lock which is released before this function returns.
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

    pub fn empty() -> Self {
        *EMPTY
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

/// An `Ident` is either:
/// - a "fresh" identifier with a unique `id` (`id >= 1`)
///   (constructed using `Ident::fresh(src, name)`, `fresh_local(name)`,
///   `ident.refresh()`, or `ident.refresh_with(f)`);
/// - a "stale" identifier with `id == 0`
///   (constructed using `Ident::stale(name)`).
///
/// Fresh identifiers are the main usage: every time we create a binder, we
/// generate a fresh identifier to guarantee that it is different from all
/// other binders.
/// That makes it easy to have capture-avoiding substitutions:
/// when we substitute under a binder, we refresh the binder.
///
/// Stale identifiers are used as a workaround for some cases where the
/// corresponding binder is not available for legacy reasons (handling of
/// `result` in postconditions and parameters in the translation of closures).
/// All of the calls to `stale()` are located in `creusot::naming`.
/// Some refactoring could get rid of them.
///
/// Another subtlety comes from serialization. Creusot serializes extern
/// specs when compiling dependencies, and then deserializes when compiling
/// the user's crate. If we just serialized `Ident` as pairs `(name, id)`,
/// and deserialize them in a different process with a new `FRESH_COUNTER`,
/// we could end up with the same `Ident` from different crates, for example
/// if `f` from a user's crate depends on a function `f` with the same name
/// in `creusot_contracts`. That's why `Ident` also contains a `src` field,
/// which is the name of the crate that created the identifier, which will be
/// different from the crate that deserializes it.
/// The `src` field is only used for disambiguation; it is not part of the
/// pretty-printed name.
///
/// This potential for collision only affects top-level bindings, whose idents
/// should be generated using `fresh`.
/// For local variables, we can use `fresh_local` which sets an empty `src`.
///
/// The `name` and `src` can be any string of `[a-zA-Z0-9_]`. Collision with
/// Why3 keywords are dealt with as late as possible, in `why3::printer`,
/// so that we can keep the original name for error messages and derived names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct Ident {
    pub(crate) name: Symbol,
    src: Symbol,
    id: u64,
}

impl Ident {
    /// Every call to `fresh` returns a new unique identifier.
    /// Use this for translating source identifiers and for generated identifiers.
    pub fn fresh(path: Symbol, name: impl AsRef<str>) -> Self {
        Ident { name: name.as_ref().into(), src: path, id: fresh_u64() }
    }

    pub fn fresh_local(name: impl AsRef<str>) -> Self {
        Self::fresh(Symbol::empty(), name)
    }

    /// Generate a fresh identifier with the same name as an existing one.
    pub fn refresh(&self) -> Self {
        Ident { name: self.name, src: self.src, id: fresh_u64() }
    }

    /// Like `refresh` with an extra function to modify the name.
    pub fn refresh_with(&self, f: impl FnOnce(String) -> String) -> Self {
        Ident { name: f(self.name.to_string()).as_str().into(), src: self.src, id: fresh_u64() }
    }

    /// All `stale` names from the same string are equal.
    pub fn stale(name: impl AsRef<str>) -> Self {
        Ident { name: name.as_ref().into(), src: *EMPTY, id: 0 }
    }

    /// Usages in Creusot:
    /// - Serialization.
    /// - Displaying the name in `expl:` labels for Why3.
    /// - Building related identifiers by appending prefixes or suffixes (`vc_`, `_lim`, etc.).
    /// - Forbidding `"result"` as an argument name.
    pub fn name(&self) -> Symbol {
        self.name
    }

    pub fn src(&self) -> Symbol {
        self.src
    }

    // Used only by serialization.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Used only by deserialization.
    pub fn unsafe_build(name: &str, path: Symbol, id: u64) -> Self {
        Ident { name: Symbol::intern(name), src: path, id }
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol::intern(s)
    }
}

impl From<Ident> for Symbol {
    fn from(id: Ident) -> Self {
        id.name
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

    pub fn parse(s: &str) -> Self {
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

    pub fn unqual(s: &str) -> Self {
        QName { module: Box::new([]), name: Symbol::intern(s) }
    }
}

impl From<QName> for Exp {
    fn from(q: QName) -> Self {
        Exp::qvar(q)
    }
}

impl<T: IntoIterator> From<T> for QName
where
    T::Item: Into<Symbol>,
{
    fn from(qname: T) -> Self {
        let qname = qname.into_iter().map(|s| s.into()).collect::<Box<[_]>>();
        let Some((&name, module)) = qname.split_last() else { panic!("Bad QName") };
        QName { module: module.into(), name }
    }
}

/// Why3 names
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub enum Name {
    /// Second field is suffix "'pre" or "'post'return'"
    Local(Ident, Option<Symbol>),
    /// Qualified name, can contain quote-suffix.
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
            Name::Local(_, Some(_)) => panic!("Cannot convert local name with suffix to Ident"),
            Name::Global(_) => panic!("Cannot convert global name to Ident"),
        }
    }
}

// Global names to intern only once.
pub(crate) static TRUE: LazyLock<Symbol> = LazyLock::new(|| Symbol::intern("true"));
pub(crate) static FALSE: LazyLock<Symbol> = LazyLock::new(|| Symbol::intern("false"));

/// A mapping from Why3 keywords to valid identifiers.
/// We use this to rename identifiers that come from Rust.
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
    "bool",    // builtin type
    "int",     // builtin type
    "string",  // builtin type
    "real",    // builtin type
    "unit",    // builtin type
    "current", // creusot prelude
    "final",   // creusot prelude
    "abstract",
    "absurd",
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

use rustc_hir::{
    def::Namespace,
    def_id::DefId,
    definitions::{DefPathData, DisambiguatedDefPathData},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use std::{iter::once, path::PathBuf};

use crate::very_stable_hash::get_very_stable_hash;

// TODO: clean up this module. There are a bunch of redundancies.
//
// The most flagrant redundancy is `value_name` vs `variable_name`.
// The difference is that `value_name` is injective, whereas `variable_name`
// is a noop for names that are already valid Why3 identifiers
// (notably when `v_` is a prefix, and with leading or trailing underscores).
// The difference seems quite cosmetic so it would be nice to somehow unify them.
//
// Q: Do we really want to be able to recover the original Rust identifier from a Why3 identifier?
// It's probably useful to preserve function (`fn`) names (for users directly and for Creusot IDE),
// but not locally bound variables (`let`, `match`, function arguments).
// Making name mangling injective everywhere used to be useful when names were just strings but
// that's no longer the case.
// For now, we do minimal changes to the handling of names as needed, until someone has a strong
// opinion about this or there is an issue that forces a more systematic refactoring.

// Why3 value names must start with a lower case letter.
// Rust function names conventionally start with a lower case letter,
// but that is not mandatory, in which case we insert a prefix `v_`.
// To make this encoding injective, also insert `v_` if the source name already starts with an `v_`.
// This makes decoding simple: if the name starts with `v_`, just strip it.
pub fn value_name(name: &str) -> String {
    if name.starts_with(|c: char| c.is_ascii_lowercase()) && !name.starts_with("v_") {
        name.to_string()
    } else {
        format!("v_{}", name)
    }
}

pub fn type_name(name: &str) -> String {
    if name.starts_with(|c: char| c.is_ascii_lowercase()) && !name.starts_with("t_") {
        name.to_string()
    } else {
        format!("t_{}", name)
    }
}

pub fn translate_accessor_name(variant: &str, field: &str) -> String {
    format!("{}__{}", type_name(&translate_name(variant)), translate_name(field))
}

// The result should be a valid Why3 identifier.
pub(crate) fn item_symb(tcx: TyCtxt, def_id: DefId, ns: Namespace) -> Symbol {
    use rustc_hir::def::DefKind::*;

    match tcx.def_kind(def_id) {
        AssocTy => tcx.item_name(def_id), // TODO: is this used (the test suite passes if I replace this with panic!)?
        Struct | Variant | Union if ns == Namespace::ValueNS => {
            Symbol::intern(&format!("C_{}", translate_name(tcx.item_name(def_id).as_str())))
        }
        Variant | Struct | Enum | Union => {
            Symbol::intern(&format!("t_{}", translate_name(tcx.item_name(def_id).as_str())))
        }
        _ => Symbol::intern(&value_name(&translate_name(tcx.item_name(def_id).as_str()))),
    }
}

/// Translate a variable name to a string of ASCII alphanumerics and underscores that starts with a lower case letter.
/// This is not injective, which is fine for variable names because they are locally bound.
pub fn variable_name(name: &str) -> String {
    // In Rust, an identifier either starts with an ASCII letter or underscore, or a non-ASCII character
    // from the set `XID_Start` in the Unicode standard, in which case `to_alphanumeric` produces a sequence
    // that start with an underscore so nothing else needs to be done.
    // Unlike `value_name` this is not injective (Both `X` and `v_X` become `v_X`).
    let name = to_alphanumeric(name);
    if name.starts_with(|c: char| c.is_ascii_lowercase() || c == '_') {
        name.to_string()
    } else {
        format!("v_{}", name)
    }
}

/// Mangle a string to consist only of ASCII alphanumerics and underscores. Code point `123` becomes `"_123_"`.
fn to_alphanumeric(n: &str) -> String {
    let mut dest = String::new();
    for c in n.chars() {
        if c.is_ascii_alphanumeric() || c == '_' {
            dest.push(c);
        } else {
            dest.push('_');
            dest.push_str(&format!("{}", c as u32));
            dest.push('_');
        }
    }
    dest
}

// Translate a name to be a valid fragment of a Why3 identifier
// Escape initial and final underscores, double underscores, non-ascii characters,
// and "qy" sequences (because "qy" is the escape sequence).
// "qy123z" encodes the code point 123.
fn push_translate_name(n: &str, dest: &mut String) -> () {
    let mut chars = n.chars().peekable();
    // Escape initial underscore
    if chars.peek() == Some(&'_') {
        let _ = chars.next();
        dest.push_str("qy95z");
    }
    while let Some(c) = chars.next() {
        let is_qy = c == 'q' && chars.peek() == Some(&'y');
        if c == '_' {
            match chars.peek() {
                None | Some('_') => dest.push_str("qy95z"),
                _ => dest.push('_'),
            }
        } else if c.is_ascii_alphanumeric() && !is_qy {
            dest.push(c);
        } else {
            dest.push_str(&format!("qy{}z", c as u32));
        }
    }
}

pub fn translate_name(n: &str) -> String {
    let mut dest = String::new();
    push_translate_name(n, &mut dest);
    dest
}

enum Segment {
    Impl(u64), // Hash of the impl subject (type for inherent impl, trait+type for trait impls)
    // There may be other variants than Impl to handle similarly.
    Other(DisambiguatedDefPathData),
}

/// Common representation of module name from which we can generate both
/// a Why3 module name (`M_krate__modl__f`) and a file name (`krate/modl/M_f.coma`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModulePath {
    path: Vec<Symbol>, // Crate and module names
    basename: Symbol,  // Function name
}

impl ModulePath {
    pub fn new(tcx: TyCtxt, def_id: DefId) -> Self {
        let mut path: Vec<Symbol> =
            ident_path_segments(tcx, def_id).into_iter().map(|s| Symbol::intern(&s)).collect();
        let basename = path.pop().unwrap();
        ModulePath { path, basename }
    }

    pub fn add_suffix(&mut self, suffix: &str) {
        self.basename = Symbol::intern(&format!("{}{}", self.basename, suffix))
    }

    // `M_krate__modl__f`
    // Note: each fragment doesn't need to go through IdentString (unlike file_name)
    pub fn why3_ident(&self) -> why3::Symbol {
        let mut path = "M_".to_owned();
        for m in &self.path {
            path += m.as_str();
            path += "__";
        }
        path += self.basename.as_str();
        why3::Symbol::intern(&path)
    }

    // `prefix/krate/modl/M_f.coma`
    // Note: pass each fragment through IdentString::from() to filter out coma keywords.
    pub fn file_name(&self, prefix: &Vec<why3::Symbol>) -> PathBuf {
        let mut path = PathBuf::new();
        for m in prefix {
            path.push(&m.to_string());
        }
        for m in &self.path {
            path.push(&m.to_string());
        }
        path.push(format!("M_{}.coma", self.basename));
        path
    }
}

fn ident_path_segments_(tcx: TyCtxt, def_id: DefId) -> Vec<Segment> {
    let mut segs = Vec::new();
    let mut id = def_id;
    loop {
        let key = tcx.def_key(id);
        let parent_id = match key.parent {
            None => break, // The last segment is CrateRoot. Skip it.
            Some(parent_id) => parent_id,
        };
        match key.disambiguated_data.data {
            DefPathData::Impl => {
                segs.push(Segment::Impl(get_very_stable_hash(&tcx.impl_subject(id), &tcx).as_u64()))
            }
            _ => segs.push(Segment::Other(key.disambiguated_data)),
        }
        id.index = parent_id;
    }
    segs.reverse();
    segs
}

pub(crate) fn ident_path_segments(tcx: TyCtxt, def_id: DefId) -> Vec<String> {
    let krate = tcx.crate_name(def_id.krate);
    once(translate_name(krate.as_str()))
        .chain(ident_path_segments_(tcx, def_id).into_iter().map(|seg| match seg {
            Segment::Impl(hash) => format!("qyi{}", hash),
            Segment::Other(data) => translate_name(&data.to_string()),
        }))
        .collect()
}

pub mod name {
    use std::sync::LazyLock;
    use why3::name::{Ident, QName};

    macro_rules! static_idents {
        ($($fn_name:ident => $string:literal),+) => {
            $(
                pub fn $fn_name() -> Ident {
                    static IDENT: LazyLock<Ident> = LazyLock::new(|| Ident::stale($string));
                    *IDENT
                }
            )+
        }
    }

    static_idents! {
        self_ => "self",
        result => "result"
    }

    macro_rules! static_qnames {
        ($($fn_name:ident => $qname:expr),+,) => {
            $(
                pub fn $fn_name() -> QName {
                    static NAME: LazyLock<QName> = LazyLock::new(|| $qname.into());
                    NAME.clone()
                }
            )+
        }
    }

    static_qnames! {
        bool => ["bool"],
        string => ["string"],
        current => ["current"],
        final_ => ["final"],
        seq_get => ["Seq", "get"],
        seq_length => ["Seq", "length"],
        seq_create => ["Seq", "create"],
    }
}

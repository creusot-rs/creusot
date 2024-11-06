use rustc_hir::{
    def::Namespace,
    def_id::DefId,
    definitions::{DefPathData, DisambiguatedDefPathData},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use why3::Ident;

use crate::very_stable_hash::get_very_stable_hash;

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
        Closure => lower_ident_path(tcx, def_id),
        _ => Symbol::intern(&value_name(&translate_name(tcx.item_name(def_id).as_str()))),
    }
}

pub(crate) fn ident_of(sym: Symbol) -> Ident {
    let mut id = sym.to_string();

    id[..1].make_ascii_lowercase();

    if sym.as_str() == id {
        Ident::build(&id)
    } else {
        id += &"'";
        Ident::build(&id)
    }
}

pub(crate) fn module_name(tcx: TyCtxt, def_id: DefId) -> Symbol {
    let kind = tcx.def_kind(def_id);
    use rustc_hir::def::DefKind::*;

    match kind {
        Ctor(_, _) | Variant => module_name(tcx, tcx.parent(def_id)),
        _ => upper_ident_path(tcx, def_id),
    }
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

fn ident_path_segments(tcx: TyCtxt, def_id: DefId) -> Vec<Segment> {
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

// This function must be injective: distinct source constructs
// must have different names in the output.
fn ident_path(upper_initial: bool, tcx: TyCtxt, def_id: DefId) -> Symbol {
    let mut dest = String::new();

    if let Some(Namespace::TypeNS) = tcx.def_kind(def_id).ns() {
        dest.push_str(if upper_initial { "T_" } else { "t_" });
    } else {
        dest.push_str(if upper_initial { "M_" } else { "m_" });
    }

    let crate_name = tcx.crate_name(def_id.krate);
    push_translate_name(crate_name.as_str(), &mut dest);

    let def_path = ident_path_segments(tcx, def_id);
    for seg in def_path.iter() {
        dest.push_str("__");
        match seg {
            Segment::Impl(hash) => dest.push_str(&format!("qyi{}", hash)),
            Segment::Other(data) => push_translate_name(&format!("{}", data), &mut dest),
        }
    }

    Symbol::intern(&dest)
}

// Coma module names must start with an upper case letter.
pub(crate) fn upper_ident_path(tcx: TyCtxt, def_id: DefId) -> Symbol {
    ident_path(true, tcx, def_id)
}

// Function and type names must start with a lower case letter.
pub(crate) fn lower_ident_path(tcx: TyCtxt, def_id: DefId) -> Symbol {
    ident_path(false, tcx, def_id)
}

pub(crate) fn anonymous_param_symbol(idx: usize) -> Symbol {
    let name = format!("_{}", idx + 1);
    Symbol::intern(&name)
}

use rustc_ast::Mutability;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Symbol;
use std::{collections::HashMap, path::PathBuf};

// * Sanitizing strings
//
// Why3 expects ASCII alphanumeric names.

// Why3 value names must start with a lower case letter.
// Rust function names conventionally start with a lower case letter,
// but that is not mandatory, in which case we insert a `prefix` (for example `v_`).
// To make this encoding injective, also insert the prefix if the source name already starts with the prefix.
// This makes decoding simple: if the name starts with the prefix, just strip it.
pub fn lowercase_prefix(prefix: &str, name: &str) -> String {
    let name = to_alphanumeric(name);
    if name.starts_with(|c: char| c.is_ascii_lowercase() || c == '_') {
        name
    } else {
        format!("{prefix}{name}")
    }
}

pub fn uppercase_prefix(prefix: &str, name: &str) -> String {
    let name = to_alphanumeric(name);
    if name.starts_with(|c: char| c.is_ascii_uppercase()) {
        name
    } else {
        format!("{prefix}{name}")
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

/// Reduce double underscores into single underscores and trim trailing underscores.
fn trim_underscores(name: &str) -> String {
    name.split('_').filter(|chunk| !chunk.is_empty()).intersperse("_").collect()
}

/// Get the sanitized `item_name` with some prefix.
pub(crate) fn ascii_item_name(prefix: &str, tcx: TyCtxt, id: DefId) -> String {
    format!("{prefix}{}", to_alphanumeric(tcx.item_name(id).as_str()))
}

// * Module paths

/// Common representation of module name from which we can generate both
/// a Why3 module name (`M_krate__modl__f`) and a file name (`krate/modl/M_f.coma`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModulePath {
    path: Vec<Symbol>,
}

impl ModulePath {
    pub fn add_suffix(&mut self, suffix: &str) {
        let basename = self.path.last_mut().unwrap();
        *basename = Symbol::intern(&format!("{}{}", basename, suffix))
    }

    // `M_krate__modl__f`
    pub fn why3_ident(&self) -> why3::Symbol {
        let mut path = "M_".to_owned();
        path.extend(self.path.iter().map(Symbol::as_str).intersperse("__"));
        why3::Symbol::intern(&path)
    }

    // `prefix/krate/modl/M_f.coma`
    pub fn file_name(&self, prefix: &Vec<why3::Symbol>) -> PathBuf {
        prefix
            .into_iter()
            .map(|s| s.to_string())
            .chain(self.path.iter().map(|s| s.to_string()))
            .collect()
    }
}

// * Global name mapping

/// Give a unique path (a sequence of `Symbol`) to every `LocalDefId`
/// that will have a Coma module (= all the `hir_body_owners()`).
///
/// We must avoid collisions otherwise we risk overwriting a Coma module
/// and missing proof obligations.
///
/// Each mapping only gives the last segment of the path for a `LocalDefId`;
/// the whole path must be reconstructed by looking up its ancestors.
///
/// Each segment must consist of alphanumerical ASCII characters
/// and not contain double underscores or trailing underscores
/// so that they can be joined unambiguously with `__`.
pub struct ComaNames(HashMap<LocalDefId, Symbol>);

impl ComaNames {
    pub fn new(tcx: TyCtxt) -> Self {
        let mut names = ComaNames(HashMap::new());
        // Map of (parent, name) to def_id
        let mut revmap = HashMap::new();
        for def_id in tcx.hir_body_owners() {
            names.add_id(tcx, &mut revmap, def_id);
        }
        names
    }

    fn add_id(
        &mut self,
        tcx: TyCtxt,
        revmap: &mut HashMap<(LocalDefId, Symbol), LocalDefId>,
        id: LocalDefId,
    ) {
        let Some(parent) = tcx.opt_local_parent(id) else {
            return; // No name for the root
        };
        if !self.contains(parent) {
            self.add_id(tcx, revmap, parent);
        }
        use rustc_hir::def::DefKind::{Impl, Trait};
        match tcx.def_kind(id) {
            Impl { .. } => {
                self.insert(revmap, parent, id, &impl_name(tcx, id));
            }
            Trait => {
                let name = ascii_item_name("trait_", tcx, id.to_def_id());
                self.insert(revmap, parent, id, &name);
            }
            _ => {
                // If it doesn't have a name (e.g., closure or promoted constant)
                // it's not something that will need its own Coma module
                let Some(name) = tcx.opt_item_name(id) else { return };
                self.insert(revmap, parent, id, &to_alphanumeric(name.as_str()));
            }
        }
    }

    fn insert(
        &mut self,
        revmap: &mut HashMap<(LocalDefId, Symbol), LocalDefId>,
        parent: LocalDefId,
        id: LocalDefId,
        name: &str,
    ) {
        let name = trim_underscores(name);
        let mut sym = Symbol::intern(&name);
        let mut i = 0;
        while revmap.try_insert((parent, sym), id).is_err() {
            sym = Symbol::intern(&format!("{name}_{i}"));
            i += 1;
        }
        self.0.insert(id, sym);
    }

    fn contains(&self, id: LocalDefId) -> bool {
        self.0.contains_key(&id)
    }

    pub fn get(&self, tcx: TyCtxt, def_id: DefId) -> ModulePath {
        match tcx.opt_parent(def_id) {
            None => ModulePath { path: Vec::new() }, // this should only happen at the root, which should always come from a recursive call, so the final `ModulePath` will be non-empty.
            Some(parent_id) => {
                let name = self.0[&def_id.expect_local()];
                let mut module = self.get(tcx, parent_id);
                module.path.push(name);
                module
            }
        }
    }
}

/// For inherent impls, generate name `impl_$TY`.
/// For trait impls, generate name `impl_$TRAIT_for_$TY`
fn impl_name<'tcx>(tcx: TyCtxt<'tcx>, id: LocalDefId) -> String {
    if let Some(trait_ref) = tcx.impl_opt_trait_ref(id.to_def_id()) {
        let trait_ref: rustc_type_ir::TraitRef<TyCtxt<'tcx>> = trait_ref.skip_binder();
        let mut name = ascii_item_name("impl_", tcx, trait_ref.def_id);
        name.push_str("_for");
        type_string(tcx, name, trait_ref.self_ty())
    } else {
        type_string(tcx, "impl".into(), tcx.type_of(id).skip_binder())
    }
}

// * Stringify type

/// Append stringified type to prefix.
///
/// Examples: with `"size_of"` as the prefix,
/// `Option<T>` becomes `"size_of_Option_T"`; `(T, U)` becomes `"size_of_tuple_T_U"`.
///
/// No need to be too rigorous. This is just used to generate more meaningful Why3 identifiers.
pub fn type_string(tcx: TyCtxt, mut prefix: String, ty: Ty) -> String {
    type_string_walk(tcx, &mut prefix, ty);
    prefix
}

fn type_string_walk(tcx: TyCtxt, prefix: &mut String, ty: Ty) {
    use rustc_type_ir::TyKind::*;
    match ty.kind() {
        Int(int_ty) => push_(prefix, int_ty.name_str()),
        Uint(uint_ty) => push_(prefix, uint_ty.name_str()),
        Float(float_ty) => push_(prefix, float_ty.name_str()),
        Bool => push_(prefix, "bool"),
        Char => push_(prefix, "char"),
        Str => push_(prefix, "str"),
        Array(ty, len) => {
            push_(prefix, "array");
            type_string_walk(tcx, prefix, *ty);
            match len.kind() {
                rustc_type_ir::ConstKind::Value(v)
                    if let ty::ValTreeKind::Leaf(scalar) = *v.valtree =>
                {
                    push_(prefix, &scalar.to_target_usize(tcx).to_string())
                }
                _ => push_(prefix, "n"),
            }
        }
        Slice(ty) => {
            push_(prefix, "slice");
            type_string_walk(tcx, prefix, *ty)
        }
        RawPtr(ty, _) => {
            push_(prefix, "ptr");
            type_string_walk(tcx, prefix, *ty)
        }
        Ref(_, ty, Mutability::Not) => {
            push_(prefix, "ref");
            type_string_walk(tcx, prefix, *ty)
        }
        Ref(_, ty, Mutability::Mut) => {
            push_(prefix, "refmut");
            type_string_walk(tcx, prefix, *ty)
        }
        Tuple(args) if args.is_empty() => {
            push_(prefix, "unit");
        }
        Tuple(args) => {
            push_(prefix, "tup");
            prefix.push_str(&args.len().to_string());
            for ty in args.iter() {
                type_string_walk(tcx, prefix, ty)
            }
        }
        Param(p) => push_(prefix, &to_alphanumeric(p.name.as_str())),
        Adt(def, args) => {
            match tcx.def_key(def.did()).get_opt_name() {
                None => push_(prefix, "UnknownAdt"),
                Some(name) => push_(prefix, &to_alphanumeric(name.as_str())),
            };
            for arg in args.iter() {
                let ty::GenericArgKind::Type(ty) = arg.kind() else { continue };
                type_string_walk(tcx, prefix, ty)
            }
        }
        Alias(_, t) => match tcx.def_key(t.def_id).get_opt_name() {
            None => push_(prefix, "opaque"),
            Some(name) => push_(prefix, &to_alphanumeric(name.as_str())),
        },
        Dynamic(traits, _) => {
            push_(prefix, "dyn");
            for tr in traits.iter() {
                let ty::ExistentialPredicate::Trait(tr) = tr.skip_binder() else { continue };
                let Some(name) = tcx.def_key(tr.def_id).get_opt_name() else { continue };
                push_(prefix, &to_alphanumeric(name.as_str()));
                break;
            }
        }
        FnDef(id, _) => push_(prefix, &ascii_item_name("", tcx, *id)),
        FnPtr(_, _) => push_(prefix, "FnPtr"),
        Closure(id, _) => {
            push_(prefix, &format!("closure{}", tcx.def_key(id).disambiguated_data.disambiguator))
        }
        Never => push_(prefix, "never"),
        _ => push_(prefix, "UnknownType"),
    };
}

fn push_(prefix: &mut String, str: &str) {
    if !prefix.is_empty() {
        prefix.push('_');
    }
    prefix.push_str(str);
}

/// Coma name for a field. Unnamed field have their index as a name.
pub(crate) fn field_name(name: &str) -> String {
    if name.as_bytes()[0].is_ascii_digit() {
        format!("f{}", name)
    } else {
        lowercase_prefix("f_", name)
    }
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
        result => "result",
        return_ => "return" // return is recognized as a keyword by the printer, but still allowed as a name for a
                            // continuation. We use this to make sure that this name never conflict with another name,
                            // and thus we can use the suffix 'post'return
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

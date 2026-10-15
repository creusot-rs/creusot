use syn::{Ident, Path, PathArguments, Visibility};

/// Returns a visibility no broader than either input.
///
/// This tries to output the broadest visibility that is allowed by both `a` and `b`. For instance,
/// `pub` and `pub(crate)` results in `pub(crate)`. However when it's not possible to determine which
/// visibility is the broadest, private is returned.
///
/// The left side is intentionally owned to make computation of minimum a bit more effictient (when
/// accumulator is passed as `a`).
pub(crate) fn intersection(a: Visibility, b: &Visibility) -> Visibility {
    match (a, b) {
        (Visibility::Inherited, _) | (_, Visibility::Inherited) => Visibility::Inherited,
        (Visibility::Public(_), b) => b.clone(),
        (a, Visibility::Public(_)) => a,
        (Visibility::Restricted(ar), Visibility::Restricted(br)) => {
            let a_path = &ar.path;
            let b_path = &br.path;

            // Every valid restricted scope is inside the current crate.
            // This also handles the equivalent spelling `pub(in crate)`.
            if a_path.is_ident("crate") {
                return Visibility::Restricted(br.clone());
            }
            if b_path.is_ident("crate") {
                return Visibility::Restricted(ar);
            }

            if let (Some((a_depth, a_tail)), Some((b_depth, b_tail))) =
                (relative_scope_path(a_path), relative_scope_path(b_path))
            {
                // A shared relative anchor gives both named suffixes the same root.
                if a_depth == b_depth {
                    if path_is_prefix(a_tail.iter().copied(), b_tail.iter().copied()) {
                        return Visibility::Restricted(br.clone());
                    }
                    if path_is_prefix(b_tail.iter().copied(), a_tail.iter().copied()) {
                        return Visibility::Restricted(ar);
                    }
                // // Pure parent paths become narrower as their hop count decreases.
                // `super` is narrower than `super::super`.
                } else if a_tail.is_empty() && b_tail.is_empty() {
                    if a_depth <= b_depth {
                        return Visibility::Restricted(ar);
                    } else {
                        return Visibility::Restricted(br.clone());
                    }
                }
            }

            // For crate-rooted paths the descendant is narrower:
            // `crate::a::b` is narrower than `crate::a`.
            if is_crate_rooted(a_path) && is_crate_rooted(b_path) {
                if path_is_prefix(path_idents(a_path), path_idents(b_path)) {
                    return Visibility::Restricted(br.clone());
                }
                if path_is_prefix(path_idents(b_path), path_idents(a_path)) {
                    return Visibility::Restricted(ar);
                }
            }

            // For all other cases we cannot tell anything better than
            // the most restrictive one, so use that.
            Visibility::Inherited
        }
    }
}

fn path_idents(path: &Path) -> impl Iterator<Item = &Ident> + ExactSizeIterator {
    path.segments.iter().map(|seg| &seg.ident)
}

/// Splits a relative scope path into parent hops and named suffix segments.
///
/// Recognizes an optional leading `self`, followed by leading `super` hops
/// and a module-name suffix. A terminal `self` denotes the preceding module.
/// The enclosing module is shared by all paths passed to the comparator.
fn relative_scope_path(path: &Path) -> Option<(usize, Vec<&Ident>)> {
    if path.leading_colon.is_some()
        // the following conditions are defensive - they are always false in the current Rust syntax
        // but if the syntax ever changes to allow these we avoid nasty surprises
        || path.segments.is_empty()
        || !path.segments.iter().all(|s| matches!(&s.arguments, PathArguments::None))
    {
        return None;
    }

    let mut segments = path.segments.iter().peekable();
    let starts_with_self = segments.peek().is_some_and(|s| s.ident == "self");
    if starts_with_self {
        segments.next();
    } else if !segments.peek().is_some_and(|s| s.ident == "super") {
        return None;
    }

    let mut parents = 0;
    while segments.peek().is_some_and(|s| s.ident == "super") {
        segments.next();
        parents += 1;
    }

    let mut suffix: Vec<_> = segments.map(|s| &s.ident).collect();
    if suffix.last().is_some_and(|ident| *ident == "self") {
        suffix.pop();
    }
    if suffix
        .iter()
        .any(|ident| *ident == "self" || *ident == "super" || *ident == "crate" || *ident == "Self")
    {
        return None;
    }

    Some((parents, suffix))
}

fn is_crate_rooted(path: &Path) -> bool {
    path.leading_colon.is_none()
        && path.segments.first().is_some_and(|s| s.ident == "crate")
        && path.segments.iter().all(|s| matches!(s.arguments, PathArguments::None))
}

/// Compare whole path segments, not text prefixes (`a` is not `ab`).
/// Called only for simple crate-rooted paths.
fn path_is_prefix<'a>(
    a: impl Iterator<Item = &'a Ident> + ExactSizeIterator,
    b: impl Iterator<Item = &'a Ident> + ExactSizeIterator,
) -> bool {
    a.len() <= b.len() && a.zip(b).all(|(a, b)| a == b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;
    use syn::{DeriveInput, parse_quote};

    fn vis(text: &str) -> Visibility {
        syn::parse_str(text).unwrap()
    }

    fn rendered(vis: &Visibility) -> String {
        quote!(#vis).to_string()
    }

    #[test]
    fn visibility_intersection() {
        let cases = [
            ("pub", "pub", "pub"),
            ("pub", "pub(crate)", "pub(crate)"),
            ("pub", "", ""),
            ("pub", "pub(self)", "pub(self)"),
            ("pub(crate)", "pub(super)", "pub(super)"),
            ("pub(in crate)", "pub(in crate::a)", "pub(in crate::a)"),
            ("pub(crate)", "pub(in super::super)", "pub(in super::super)"),
            ("pub(in crate::a)", "pub(in crate::a::b)", "pub(in crate::a::b)"),
            ("pub(super)", "pub(in super::super)", "pub(super)"),
            ("pub(in self::super)", "pub(in super::super)", "pub(in self::super)"),
            (
                "pub(in super::super::foo)",
                "pub(in super::super::foo::bar)",
                "pub(in super::super::foo::bar)",
            ),
            ("pub(in super::super)", "pub(in super::super::foo)", "pub(in super::super::foo)"),
            (
                "pub(in self::super::super::foo)",
                "pub(in super::super::foo::bar)",
                "pub(in super::super::foo::bar)",
            ),
            (
                "pub(in super::super::foo::self)",
                "pub(in super::super::foo::bar)",
                "pub(in super::super::foo::bar)",
            ),
            // Divergent suffixes cannot both designate ancestors at one site.
            ("pub(in super::super::foo)", "pub(in super::super::foobar)", ""),
            // Different relative anchors with named suffixes stay conservative.
            ("pub(in super::super::foo)", "pub(in super::bar)", ""),
            // Mixed absolute/relative paths stay conservative.
            ("pub(in crate::a)", "pub(super)", ""),
            ("pub(in crate::a)", "pub(in crate::ab)", ""),
        ];

        for (a, b, expected) in cases {
            let (av, bv, ev) = (vis(a), vis(b), vis(expected));
            assert_eq!(rendered(&intersection(av.clone(), &bv)), rendered(&ev), "{a} / {b}");
            assert_eq!(rendered(&intersection(bv, &av)), rendered(&ev), "{b} / {a}");
        }
    }
}

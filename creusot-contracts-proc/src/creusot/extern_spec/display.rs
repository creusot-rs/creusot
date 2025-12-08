//! Display various parsed items for use in documentation links

pub(super) struct DisplayPath<'a>(pub(super) &'a syn::Path);
impl std::fmt::Display for DisplayPath<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.0.leading_colon.is_some() {
            f.write_str("::")?;
        }
        for (i, c) in self.0.segments.iter().enumerate() {
            if i != 0 {
                f.write_str("::")?;
            }
            write!(f, "{}", c.ident)?;
            match &c.arguments {
                syn::PathArguments::None => {}
                syn::PathArguments::AngleBracketed(args) => {
                    if !args.args.is_empty() {
                        f.write_str("<")?;
                        for (i, a) in args.args.iter().enumerate() {
                            if i != 0 {
                                f.write_str(", ")?;
                            }
                            write!(f, "{}", DisplayGenericArg(a))?;
                        }
                        f.write_str(">")?;
                    }
                }
                syn::PathArguments::Parenthesized(args) => {
                    f.write_str("(")?;
                    for (i, a) in args.inputs.iter().enumerate() {
                        if i != 0 {
                            f.write_str(", ")?;
                        }
                        write!(f, "{}", DisplayType(a))?;
                    }
                    f.write_str(")")?;
                    if let syn::ReturnType::Type(_, out) = &args.output {
                        write!(f, " -> {}", DisplayType(out))?;
                    }
                }
            }
        }
        Ok(())
    }
}

pub(super) struct DisplayType<'a>(pub(super) &'a syn::Type);
impl std::fmt::Display for DisplayType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            syn::Type::Array(a) => write!(f, "[{}; _]", DisplayType(&a.elem)),
            syn::Type::BareFn(_) => write!(f, "fn"),
            syn::Type::Group(g) => write!(f, "{}", DisplayType(&g.elem)),
            syn::Type::ImplTrait(i) => {
                f.write_str("impl ")?;
                for (i, b) in i.bounds.iter().enumerate() {
                    if i != 0 {
                        f.write_str(" + ")?;
                    }
                    match b {
                        syn::TypeParamBound::Trait(_) => f.write_str("UNSUPPORTED"),
                        syn::TypeParamBound::Lifetime(l) => write!(f, "'{}", l.ident),
                        syn::TypeParamBound::PreciseCapture(_) => write!(f, "use <UNSUPPORTED>"),
                        syn::TypeParamBound::Verbatim(ts) => write!(f, "{ts}"),
                        _ => f.write_str("UNSUPPORTED"),
                    }?;
                }
                Ok(())
            }
            syn::Type::Infer(_) => f.write_str("_"),
            syn::Type::Macro(m) => write!(f, "{}", m.mac.tokens),
            syn::Type::Never(_) => f.write_str("!"),
            syn::Type::Paren(t) => write!(f, "({})", DisplayType(&t.elem)),
            syn::Type::Path(p) => {
                if let Some(qself) = &p.qself {
                    write!(f, "<{}>", DisplayType(&qself.ty))?;
                }
                if p.path.leading_colon.is_none() && p.qself.is_some() {
                    f.write_str("::")?;
                }
                write!(f, "{}", DisplayPath(&p.path))
            }
            syn::Type::Ptr(p) => write!(f, "pointer<{}>", DisplayType(&p.elem)),
            syn::Type::Reference(r) => write!(
                f,
                "&{}{}",
                if r.mutability.is_some() { "mut " } else { "" },
                DisplayType(&r.elem)
            ),
            syn::Type::Slice(s) => write!(f, "slice<{}>", DisplayType(&s.elem)),
            syn::Type::TraitObject(_) => f.write_str("UNSUPPORTED"),
            syn::Type::Tuple(t) => {
                f.write_str("(")?;
                for (i, t) in t.elems.iter().enumerate() {
                    if i != 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", DisplayType(t))?;
                }
                if t.elems.len() == 1 {
                    f.write_str(",")?;
                }
                f.write_str(")")
            }
            syn::Type::Verbatim(ts) => write!(f, "{ts}"),
            _ => f.write_str("UNSUPPORTED"),
        }
    }
}

pub(super) struct DisplayGenericArg<'a>(pub(super) &'a syn::GenericArgument);
impl std::fmt::Display for DisplayGenericArg<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            syn::GenericArgument::Lifetime(l) => write!(f, "'{}", l.ident),
            syn::GenericArgument::Type(t) => write!(f, "{}", DisplayType(t)),
            syn::GenericArgument::Const(_) => f.write_str("UNSUPPORTED"),
            syn::GenericArgument::AssocType(_) => f.write_str("UNSUPPORTED"),
            syn::GenericArgument::AssocConst(_) => f.write_str("UNSUPPORTED"),
            syn::GenericArgument::Constraint(_) => f.write_str("UNSUPPORTED"),
            _ => f.write_str("UNSUPPORTED"),
        }
    }
}

use proc_macro::TokenStream as TS1;
use proc_macro2::TokenStream;
use syn::{
    Attribute, GenericArgument, Generics, Ident, Lifetime, Path, PathArguments, QSelf, ReturnType,
    Type,
};

/// The body of a logical function or a spec.
pub(crate) enum LogicBody {
    Some(TS1),
    /// The function does not have a body. For example, if it is a trait function.
    None,
    /// The function has a body, but it is ignored because the function is `#[trusted]`
    Trusted,
}

/// Generates a piece of documentation corresponding to the spec.
pub(crate) fn document_spec(spec_name: &str, spec: LogicBody) -> TokenStream {
    let spec_color = match spec_name {
        "requires" => "Tomato",
        "ensures" => "DodgerBlue",
        "terminates" | "pure" | "logic" | "logic(prophetic)" | "law" => "Violet",
        _ => "LightGray",
    };
    let spec_name =
        format!("> <span style=\"color:{spec_color};\"><samp>{spec_name}</samp></span>");
    let spec = match spec {
        LogicBody::Some(s) if !s.is_empty() => s,
        _ => {
            return quote::quote! {
                #[cfg_attr(not(doctest), doc = "")]
                #[cfg_attr(not(doctest), doc = #spec_name)]
                #[cfg_attr(not(doctest), doc = "")]
            }
        }
    };
    let mut spec = {
        let mut span = None;
        for t in spec {
            match span {
                None => span = Some(t.span()),
                Some(s) => span = s.join(t.span()),
            }
        }
        let mut res = span.unwrap().source_text().unwrap();
        // hack to handle logic functions
        if res.starts_with("{\n") && res.ends_with("}") {
            let body = res[2..res.len() - 1].trim_end();
            let mut leading_whitespace = usize::MAX;
            for line in body.lines() {
                leading_whitespace =
                    std::cmp::min(leading_whitespace, line.len() - line.trim_start().len());
            }
            let mut trimmed_res = String::new();
            for line in body.lines() {
                trimmed_res.push_str(&line[leading_whitespace..]);
                trimmed_res.push('\n');
            }
            res = trimmed_res;
        }
        res
    };
    spec = spec.replace('\n', "\n> > ");
    spec = format!("> > ```\n> > {spec}\n> > ```");
    quote::quote! {
        #[cfg_attr(not(doctest), doc = "")]
        #[cfg_attr(not(doctest), doc = #spec_name)]
        #[cfg_attr(not(doctest), doc = #spec)]
    }
}

pub(crate) fn is_trusted(attrs: &[Attribute]) -> bool {
    for attr in attrs {
        let path = attr.path();

        if path.is_ident("trusted")
            || (path.segments.len() == 3
                && path
                    .segments
                    .iter()
                    .zip(["creusot", "decl", "trusted"])
                    .all(|(s1, s2)| s1.ident == s2))
        {
            return true;
        }
    }
    false
}

/// Create an item name from a type or a trait.
#[derive(Clone)]
pub(crate) struct DocItemName(pub(crate) String);

impl DocItemName {
    pub(crate) fn add_ident(&mut self, i: &Ident) {
        self.0.push('_');
        self.0.push_str(&i.to_string());
    }

    pub(crate) fn add_type(&mut self, ty: &Type) {
        match ty {
            Type::Array(type_array) => {
                self.0.push_str("__array");
                self.add_type(&type_array.elem);
            }
            Type::BareFn(type_bare_fn) => {
                self.0.push_str("__fn");
                for input in &type_bare_fn.inputs {
                    self.add_type(&input.ty);
                }
                self.add_return_type(&type_bare_fn.output);
            }
            Type::Group(type_group) => self.add_type(&type_group.elem),
            Type::ImplTrait(type_impl_trait) => {
                self.0.push_str("__impl");
                for bound in &type_impl_trait.bounds {
                    self.add_type_param_bound(bound);
                }
            }
            Type::Infer(_) => unreachable!(),
            Type::Macro(_) => self.0.push_str("__macro"),
            Type::Never(_) => {
                self.0.push_str("__never");
            }
            Type::Paren(type_paren) => self.add_type(&type_paren.elem),
            Type::Path(type_path) => {
                self.add_path(&type_path.path);
                self.add_qself(&type_path.qself)
            }
            Type::Ptr(type_ptr) => {
                if type_ptr.mutability.is_some() {
                    self.0.push_str("__ptrmut");
                } else {
                    self.0.push_str("__ptrconst");
                }
                self.add_type(&type_ptr.elem);
            }
            Type::Reference(type_reference) => {
                if type_reference.mutability.is_some() {
                    self.0.push_str("__refmut");
                } else {
                    self.0.push_str("__ref");
                }
                self.add_type(&type_reference.elem);
            }
            Type::Slice(type_slice) => {
                self.0.push_str("__slice");
                self.add_type(&type_slice.elem);
            }
            Type::TraitObject(_) => unimplemented!(),
            Type::Tuple(type_tuple) => {
                self.0.push_str(&format!("__tuple{}", type_tuple.elems.len()));
                for ty in &type_tuple.elems {
                    self.add_type(ty);
                }
            }
            Type::Verbatim(_) => unimplemented!(),
            _ => todo!(),
        }
    }

    pub(crate) fn add_generics(&mut self, generics: &Generics) {
        for param in &generics.params {
            self.add_generic_param(param);
        }
    }

    pub(crate) fn add_generic_param(&mut self, param: &syn::GenericParam) {
        match param {
            syn::GenericParam::Lifetime(lifetime_param) => {
                self.add_lifetime(&lifetime_param.lifetime);
                if !lifetime_param.bounds.is_empty() {
                    self.0.push_str("__outlives");
                    for lifetime in &lifetime_param.bounds {
                        self.add_lifetime(lifetime);
                    }
                }
            }
            syn::GenericParam::Type(type_param) => {
                self.add_ident(&type_param.ident);
                // if !type_param.bounds.is_empty() {
                //     self.0.push_str("__implements");
                //     for bound in &type_param.bounds {
                //         self.add_type_param_bound(bound);
                //     }
                // }
            }
            syn::GenericParam::Const(const_param) => {
                self.0.push_str("__const");
                self.0.push_str(&const_param.ident.to_string());
            }
        }
    }

    fn add_type_param_bound(&mut self, bound: &syn::TypeParamBound) {
        match bound {
            syn::TypeParamBound::Trait(trait_bound) => self.add_path(&trait_bound.path),
            syn::TypeParamBound::Lifetime(lifetime) => self.add_lifetime(lifetime),
            syn::TypeParamBound::Verbatim(_) => unimplemented!(),
            _ => todo!(),
        }
    }

    fn add_return_type(&mut self, return_ty: &ReturnType) {
        self.0.push_str("__output");
        match &return_ty {
            ReturnType::Default => self.0.push_str("__unit"),
            ReturnType::Type(_, ty) => self.add_type(ty),
        }
    }

    pub(crate) fn add_path(&mut self, path: &Path) {
        for segment in &path.segments {
            self.add_ident(&segment.ident);
            match &segment.arguments {
                PathArguments::None => {}
                PathArguments::AngleBracketed(generic_args) => {
                    for arg in &generic_args.args {
                        match arg {
                            GenericArgument::Lifetime(lifetime) => self.add_lifetime(lifetime),
                            GenericArgument::Type(ty) => self.add_type(ty),
                            GenericArgument::Const(_) => todo!(),
                            GenericArgument::AssocType(_) => todo!(),
                            GenericArgument::AssocConst(_) => todo!(),
                            GenericArgument::Constraint(_) => todo!(),
                            _ => todo!(),
                        }
                    }
                }
                PathArguments::Parenthesized(generic_args) => {
                    self.0.push_str("__lpar");
                    for arg in &generic_args.inputs {
                        self.add_type(arg);
                    }
                    self.0.push_str("__rpar");
                    self.add_return_type(&generic_args.output)
                }
            }
        }
    }

    pub(crate) fn add_qself(&mut self, qself: &Option<QSelf>) {
        if let Some(qself) = qself {
            self.add_type(&qself.ty);
        }
    }

    // If there ever is a need to disambiguate on lifetime parameters, uncomment this
    fn add_lifetime(&mut self, _lifetime: &Lifetime) {
        // self.0.push_str("__lifetime");
        // self.0.push_str(&lifetime.ident.to_string());
    }
}

use proc_macro::TokenStream as TS1;
use proc_macro2::TokenStream;

/// Generates a piece of documentation corresponding to the spec.
pub(crate) fn document_spec(spec_name: &str, spec: TS1) -> TokenStream {
    let spec_color = match spec_name {
        "requires" => "Tomato",
        "ensures" => "DodgerBlue",
        "terminates" | "pure" | "logic" | "logic(prophetic)" => "Violet",
        _ => "LightGray",
    };
    let spec_name =
        format!("> <span style=\"color:{spec_color};\"><samp>{spec_name}</samp></span>");
    if spec.is_empty() {
        return quote::quote! {
            #[cfg_attr(not(doctest), doc = "")]
            #[cfg_attr(not(doctest), doc = #spec_name)]
            #[cfg_attr(not(doctest), doc = "")]
        };
    }
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

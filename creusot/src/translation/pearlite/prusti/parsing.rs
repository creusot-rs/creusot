use crate::error::{CreusotResult, Error};
use creusot_rustc::{ast::Lit, span::Symbol};

fn skip_space(rest: &mut &str) {
    let idx = rest.find(|c: char| c != ' ').unwrap_or(rest.len());
    *rest = &rest[idx..];
}

pub(super) type Home = Symbol;

pub(super) type HomeSig = (Vec<Home>, Home);

fn parse_home(rest: &mut &str, counter: &mut u32) -> Option<Home> {
    let after = rest.strip_prefix("'")?;
    let idx = after
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '!'))
        .unwrap_or(after.len())
        + 1;
    let home = match &rest[..idx] {
        "'_" => {
            let res = Symbol::intern(&format!("'{counter}h"));
            *counter += 1;
            res
        }
        other => Symbol::intern(other),
    };
    *rest = &rest[idx..];
    Some(home)
}

fn parse_home_tuple(rest: &mut &str, counter: &mut u32) -> Option<Vec<Home>> {
    *rest = rest.strip_prefix("(")?;
    let mut res = Vec::new();
    skip_space(rest);
    match rest.strip_prefix(")") {
        Some(r) => {
            *rest = r;
            return Some(res);
        }
        None => {}
    };
    loop {
        skip_space(rest);
        res.push(parse_home(rest, counter)?);
        skip_space(rest);
        match rest.strip_prefix(",") {
            Some(r) => *rest = r,
            None => break,
        }
    }
    skip_space(rest);
    *rest = rest.strip_prefix(")")?;
    Some(res)
}

fn parse_home_sig(rest: &mut &str) -> Option<HomeSig> {
    let mut counter = 0;
    skip_space(rest);
    let args = parse_home_tuple(rest, &mut counter)?;
    skip_space(rest);
    *rest = rest.strip_prefix("->")?;
    skip_space(rest);
    let res = parse_home(rest, &mut counter)?;
    skip_space(rest);
    if rest.is_empty() {
        Some((args, res))
    } else {
        None
    }
}

pub(super) fn parse_home_sig_lit(sig: &Lit) -> CreusotResult<(Vec<Home>, Home)> {
    let mut s = sig.token_lit.symbol.as_str();
    parse_home_sig(&mut s)
        .ok_or_else(|| Error::new(sig.span, format!("invalid home signature, reached \"{s}\"")))
}
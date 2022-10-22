use super::{Home, Lattice::*, Region, TimeSlice::*};
use crate::error::{CreusotResult, Error};
use creusot_rustc::{ast::Lit, span::Symbol};

fn skip_space(rest: &mut &str) {
    let idx = rest.find(|c: char| c != ' ').unwrap_or(rest.len());
    *rest = &rest[idx..];
}

fn parse_home(rest: &mut &str) -> Option<Home> {
    let after = rest.strip_prefix("'")?;
    let idx = after
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '!'))
        .unwrap_or(after.len())
        + 1;
    let home = match &rest[..idx] {
        "'curr" => Inner(Curr),
        "'_" => Unknown,
        "'!" => Absurd,
        other => Inner(Expiry(Region::Named(Symbol::intern(other)))),
    };
    *rest = &rest[idx..];
    Some(home)
}

fn parse_home_tuple(rest: &mut &str) -> Option<Vec<Home>> {
    *rest = rest.strip_prefix("(")?;
    let mut res = Vec::new();
    loop {
        skip_space(rest);
        res.push(parse_home(rest)?);
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

fn parse_home_sig(rest: &mut &str) -> Option<(Vec<Home>, Home)> {
    skip_space(rest);
    let args = parse_home_tuple(rest)?;
    skip_space(rest);
    *rest = rest.strip_prefix("->")?;
    skip_space(rest);
    let res = parse_home(rest)?;
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

use crate::error::{CreusotResult, Error};
use rustc_ast::MetaItemLit as Lit;
use rustc_span::Symbol;
use std::fmt::{Debug, Formatter};
pub(super) type Home = Symbol;
#[derive(Debug, Copy, Clone)]
pub(super) struct Outlives {
    pub long: Home,
    pub short: Home,
}

pub(super) struct HomeSig {
    data: Vec<Home>,
    bounds_start: usize,
}

impl HomeSig {
    pub(super) fn args(&self) -> impl Iterator<Item = Home> + Clone + '_ {
        self.data[0..self.bounds_start].iter().copied()
    }

    pub(super) fn args_len(&self) -> usize {
        self.bounds_start
    }

    pub(super) fn bounds(&self) -> impl Iterator<Item = Outlives> + Clone + '_ {
        self.data[self.bounds_start..].chunks_exact(2).map(|x| match x {
            &[long, short] => Outlives { long, short },
            _ => unreachable!(),
        })
    }

    fn new(args: Vec<Home>) -> Self {
        let len = args.len();
        HomeSig { data: args, bounds_start: len }
    }

    fn add_bound(&mut self, bound: Outlives) {
        self.data.push(bound.long);
        self.data.push(bound.short);
    }
}

struct DebugCopyIter<Iter>(Iter);

impl<Iter: Clone + Iterator> Debug for DebugCopyIter<Iter>
where
    Iter::Item: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.0.clone()).finish()
    }
}

impl Debug for HomeSig {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HomeSig")
            .field("homes", &DebugCopyIter(self.args()))
            .field("bounds", &DebugCopyIter(self.bounds()))
            .finish()
    }
}

fn skip_space(rest: &mut &str) {
    let idx = rest.find(|c: char| c != ' ').unwrap_or(rest.len());
    *rest = &rest[idx..];
}

fn parse_lit(rest: &mut &str, lit: &str) -> Option<()> {
    match rest.strip_prefix(lit) {
        Some(r) => {
            *rest = r;
            skip_space(rest);
            Some(())
        }
        None => None,
    }
}

fn parse_home(rest: &mut &str, mut handle_blank: impl FnMut() -> Option<Home>) -> Option<Home> {
    skip_space(rest);
    let after = rest.strip_prefix("'")?;
    let idx =
        after.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(after.len()) + 1;
    let home = match &rest[..idx] {
        "'_" => handle_blank()?,
        other => Symbol::intern(other),
    };
    *rest = &rest[idx..];
    skip_space(rest);
    Some(home)
}

fn parse_home_list(rest: &mut &str, counter: &mut u32) -> Option<Vec<Home>> {
    let mut res = Vec::new();
    let mut handle_blank = || {
        let res = Symbol::intern(&format!("'{counter}h"));
        *counter += 1;
        Some(res)
    };
    loop {
        res.push(parse_home(rest, &mut handle_blank)?);
        if parse_lit(rest, ",").is_none() {
            break;
        }
    }
    Some(res)
}

fn parse_bounds(rest: &mut &str, sig: &mut HomeSig) -> Option<()> {
    loop {
        let long = parse_home(rest, || None)?;
        parse_lit(rest, ":")?;
        loop {
            let short = parse_home(rest, || None)?;
            sig.add_bound(Outlives { long, short });
            if parse_lit(rest, "+").is_none() {
                break;
            }
        }
        if parse_lit(rest, ",").is_none() {
            break;
        }
    }
    Some(())
}

fn parse_home_sig(rest: &mut &str) -> Option<HomeSig> {
    let mut counter = 0;
    skip_space(rest);
    let args = parse_home_list(rest, &mut counter)?;
    let mut sig = HomeSig::new(args);
    if parse_lit(rest, "where").is_some() {
        parse_bounds(rest, &mut sig)?;
    }
    if rest.is_empty() {
        Some(sig)
    } else {
        None
    }
}

pub(super) fn parse_home_sig_lit(sig: &Lit) -> CreusotResult<Option<HomeSig>> {
    let s = sig.as_token_lit().symbol;
    let mut s = s.as_str();
    if s.is_empty() {
        return Ok(None);
    }
    match parse_home_sig(&mut s) {
        None => Err(Error::new(sig.span, format!("invalid home signature, reached \"{s}\""))),
        Some(h) => Ok(Some(h)),
    }
}

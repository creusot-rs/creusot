use crate::{
    error::{CreusotResult, Error},
    prusti::{
        parsing,
        parsing::Home,
        types::{Ctx, Ty},
    },
    util,
};
use itertools::Either;
use rustc_ast::MetaItemLit as Lit;
use rustc_middle::ty::{Binder, FnSig, InternalSubsts, Region};
use rustc_span::{def_id::DefId, symbol::Ident, Symbol, DUMMY_SP};
use std::iter;

type TimeSlice<'tcx> = Region<'tcx>;

/// Returns region corresponding to `l`
/// Also checks that 'curr is not blocked
fn make_time_slice<'tcx>(
    l: &Lit,
    regions: impl Iterator<Item = Region<'tcx>>,
    ctx: &mut Ctx<'tcx>,
) -> CreusotResult<TimeSlice<'tcx>> {
    let mut bad_curr = false;
    let old_region = ctx.old_region();
    let curr_region = ctx.curr_region();
    let mut regions = regions.map(|r| {
        bad_curr = bad_curr || ctx.check_ok_in_program(r);
        (r.get_name(), ctx.fix_region(r))
    });
    let sym = l.as_token_lit().symbol;
    let res = match sym.as_str() {
        "old" => Ok(old_region),
        "curr" => Ok(curr_region),
        "'_" => {
            let mut candiates = (&mut regions).filter(|(r, fix)| *r == None && *fix != curr_region);
            match (candiates.next(), candiates.next()) {
                (None, _) => Err(Error::new(l.span, "function has no blocked anonymous regions")),
                (Some(_), Some(_)) => {
                    Err(Error::new(l.span, "function has multiple blocked anonymous regions"))
                }
                (Some((_, r)), None) => Ok(r),
            }
        }
        _ => {
            if let Some((_, r)) = regions.find(|(r, _)| *r == Some(sym)) {
                Ok(r)
            } else {
                Err(Error::new(l.span, format!("use of undeclared lifetime name {sym}")))
            }
        }
    };
    regions.for_each(drop);
    if bad_curr {
        Err(Error::new(l.span, "'curr region must not be blocked"))
    } else {
        res
    }
}

/// Returns region corresponding to `l` in a logical context
fn make_time_slice_logic<'tcx>(l: &Lit, ctx: &mut Ctx<'tcx>) -> CreusotResult<TimeSlice<'tcx>> {
    let sym = l.as_token_lit().symbol;
    match sym.as_str() {
        "old" => Ok(ctx.curr_region()), //hack requires clauses to use same time slice as return
        "curr" => Ok(ctx.curr_region()),
        "'_" => Err(Error::new(
            l.span,
            "expiry contract on logic function must use a concrete lifetime/home",
        )),
        _ => Ok(ctx.home_to_region(sym)),
    }
}

fn add_homes_to_sig<'a, 'tcx>(
    ctx: &'a mut Ctx<'tcx>,
    sig: FnSig<'tcx>,
    home_sig: Option<&Lit>,
) -> CreusotResult<(impl Iterator<Item = (Symbol, CreusotResult<Ty<'tcx>>)> + 'a, Ty<'tcx>)> {
    let args: &[Ident] = ctx.tcx.fn_arg_names(ctx.owner_id);
    let (arg_homes, ret_home, span) = match home_sig {
        Some(lit) => {
            let (arg_homes, ret_home) = parsing::parse_home_sig_lit(lit)?;
            if arg_homes.len() != args.len() {
                return Err(Error::new(lit.span, "number of args doesn't match signature"));
            }
            let home = ctx.map_parsed_home(ret_home);
            (
                Either::Left(arg_homes.into_iter().map(move |h| ctx.map_parsed_home(h))),
                home,
                lit.span,
            )
        }
        None => {
            let arg_homes = iter::repeat(Home { data: ctx.old_region(), is_ref: false });
            (Either::Right(arg_homes), Home { data: ctx.curr_region(), is_ref: false }, DUMMY_SP)
        }
    };
    let types =
        sig.inputs().iter().zip(arg_homes).map(move |(&ty, home)| Ty::try_new(ty, home, span));

    let args = args
        .iter()
        .enumerate()
        .map(|(idx, arg)| {
            if arg.name.is_empty() {
                let name = format!("{}", util::AnonymousParamName(idx));
                Symbol::intern(&name)
            } else {
                arg.name
            }
        })
        .zip(types);
    Ok((args, Ty::try_new(sig.output(), ret_home, span)?))
}

pub(crate) fn full_signature<'a, 'tcx>(
    home_sig: Option<&Lit>,
    sig: Binder<'tcx, FnSig<'tcx>>,
    ts: &Lit,
    owner_id: DefId,
    ctx: &'a mut Ctx<'tcx>,
) -> CreusotResult<(
    Region<'tcx>,
    impl Iterator<Item = (Symbol, CreusotResult<Ty<'tcx>>)> + 'a,
    Ty<'tcx>,
)> {
    let tcx = ctx.tcx;
    let bound_vars = sig.bound_vars();
    let lifetimes1 = bound_vars.iter().map(|bvk| tcx.mk_re_free(owner_id, bvk.expect_region()));
    let lifetimes2 = InternalSubsts::identity_for_item(tcx, owner_id).regions();
    let lifetimes = lifetimes1.chain(lifetimes2);

    let sig = tcx.liberate_late_bound_regions(owner_id, sig);
    let sig = ctx.fix_regions(sig);

    let (ts, home_sig) = match home_sig {
        Some(lit) => (make_time_slice_logic(ts, ctx)?, Some(lit)),
        None => (make_time_slice(ts, lifetimes, ctx)?, None),
    };
    //dbg!(&non_blocked);
    //eprintln!("{:?}", sig);
    let (arg_tys, res_ty) = add_homes_to_sig(ctx, sig, home_sig)?;
    Ok((ts, arg_tys, res_ty))
}

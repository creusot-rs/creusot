use crate::{
    error::{CreusotResult, Error},
    prusti::{
        parsing,
        parsing::Home,
        types::{Ctx, PreCtx, Ty},
    },
    util,
};
use rustc_ast::MetaItemLit as Lit;
use rustc_middle::ty::{Binder, FnSig, Region, TyCtxt};
use rustc_span::{def_id::DefId, symbol::Ident, Span, Symbol, DUMMY_SP};
use std::iter;

type TimeSlice<'tcx> = Region<'tcx>;

/// Returns region corresponding to `l`
/// Also checks that 'curr is not blocked
fn make_time_slice<'tcx>(l: &Lit, ctx: &Ctx<'tcx>) -> CreusotResult<TimeSlice<'tcx>> {
    let old_region = ctx.old_region();
    let curr_region = ctx.curr_region();
    let mut regions = ctx.base_regions().map(|r| (r.get_name(), ctx.fix_region(r)));
    let sym = l.as_token_lit().symbol;
    match sym.as_str() {
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
    }
}

/// Returns region corresponding to `l` in a logical context
fn make_time_slice_logic<'tcx>(l: &Lit, ctx: &mut PreCtx<'tcx>) -> CreusotResult<TimeSlice<'tcx>> {
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
    args: &'tcx [Ident],
    sig: FnSig<'tcx>,
    arg_homes: impl Iterator<Item = Home<Region<'tcx>>>,
    ret_home: Home<Region<'tcx>>,
    span: Span,
) -> CreusotResult<(impl Iterator<Item = (Symbol, CreusotResult<Ty<'tcx>>)>, Ty<'tcx>)> {
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
    tcx: TyCtxt<'tcx>,
    sig: Binder<'tcx, FnSig<'tcx>>,
    ts: &Lit,
    owner_id: DefId,
) -> CreusotResult<(
    Ctx<'tcx>,
    Region<'tcx>,
    impl Iterator<Item = (Symbol, CreusotResult<Ty<'tcx>>)>,
    Ty<'tcx>,
)> {
    let ctx = Ctx::new_for_spec(tcx, owner_id)?;
    let sig = tcx.liberate_late_bound_regions(owner_id, sig);
    let sig = ctx.fix_regions(sig);

    let ts = make_time_slice(ts, &ctx)?;
    let arg_homes = iter::repeat(ctx.old_region().into());
    let ret_home = ctx.curr_region().into();
    let args = ctx.tcx.fn_arg_names(ctx.owner_id);
    let (arg_tys, res_ty) = add_homes_to_sig(args, sig, arg_homes, ret_home, DUMMY_SP)?;
    Ok((ctx, ts, arg_tys, res_ty))
}

pub(crate) fn full_signature_logic<'a, 'tcx, T: FromIterator<(Symbol, Ty<'tcx>)>>(
    tcx: TyCtxt<'tcx>,
    home_sig: &Lit,
    sig: Binder<'tcx, FnSig<'tcx>>,
    ts: &Lit,
    owner_id: DefId,
) -> CreusotResult<(Ctx<'tcx>, Region<'tcx>, T, Ty<'tcx>)> {
    let mut ctx = PreCtx::new(tcx, owner_id);
    let sig = tcx.liberate_late_bound_regions(owner_id, sig);
    let sig = ctx.fix_regions(sig);

    let ts = make_time_slice_logic(ts, &mut ctx)?;

    let (arg_homes, ret_home) = parsing::parse_home_sig_lit(home_sig)?;
    if arg_homes.len() != sig.inputs().len() {
        return Err(Error::new(home_sig.span, "number of args doesn't match signature"));
    }
    let ret_home = ctx.map_parsed_home(ret_home);
    let args = ctx.tcx.fn_arg_names(ctx.owner_id);
    let arg_homes = arg_homes.into_iter().map(|h| ctx.map_parsed_home(h));

    let (arg_tys, res_ty) = add_homes_to_sig(args, sig, arg_homes, ret_home, home_sig.span)?;
    let arg_tys = arg_tys.map(|(k, v)| v.map(|v| (k, v))).collect::<CreusotResult<T>>()?;
    Ok((ctx.finish_for_logic(), ts, arg_tys, res_ty))
}

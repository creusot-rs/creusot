//! Special symbols defined in [`creusot_contracts`] and annotated with
//! `#[rustc_diagnostic_item = "..."]`

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::Symbol;

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum AreContractsLoaded {
    Yes,
    No,
    MissingItems(Vec<String>),
}

macro_rules! contracts_items {
    (
        $(
            $kind:tt $name:path [ $symbol:literal ] $is_name:ident $get_name:ident
        )*
    ) => {
        $(
            #[doc = concat!("Check if `def_id` is the `", stringify!($name), "` ", contracts_items!(@kind $kind))]
            #[allow(unused)]
            pub(crate) fn $is_name(tcx: TyCtxt, def_id: DefId) -> bool {
                tcx.is_diagnostic_item(Symbol::intern($symbol), def_id)
            }

            #[doc = concat!("Get the id of the `", stringify!($name), "` ", contracts_items!(@kind $kind))]
            #[allow(unused)]
            pub(crate) fn $get_name(tcx: TyCtxt) -> DefId {
                tcx.get_diagnostic_item(Symbol::intern($symbol)).unwrap()
            }
        )*

        /// Call this at the earlist point possible: if `creusot-contracts` is not loaded, we
        /// need to immediatly crash.
        pub(crate) fn are_contracts_loaded(tcx: TyCtxt) -> AreContractsLoaded {
            let mut missing_items = Vec::new();
            let mut no_items = true;
            for symbol in [$($symbol),*] {
                if tcx.get_diagnostic_item(Symbol::intern(symbol)).is_some() {
                    no_items = false;
                } else {
                    missing_items.push(symbol.to_string());
                }
            }
            if no_items {
                AreContractsLoaded::No
            } else if !missing_items.is_empty() {
                AreContractsLoaded::MissingItems(missing_items)
            } else {
                AreContractsLoaded::Yes
            }
        }
    };
    (@kind fn) => { "function" };
    (@kind type) => { "type" };
}

contracts_items! {
    fn inv                     ["creusot_invariant_internal"]
        is_inv_function       get_inv_function
    fn resolve                 ["creusot_resolve"]
        is_resolve_function   get_resolve_function
    fn structural_resolve      ["creusot_structural_resolve"]
        is_structural_resolve get_structural_resolve
    fn invariant               ["creusot_invariant_user"]
        is_invariant_method   get_invariant_method
    fn resolve                 ["creusot_resolve_method"]
        is_resolve_method     get_resolve_method
    fn FnMut::unnest           ["fn_mut_impl_unnest"]
        is_fn_mut_unnest      get_fn_mut_unnest
    fn Snapshot::new           ["snapshot_new"]
        is_snaphot_new        get_snaphot_new
    fn Snapshot::from_fn       ["snapshot_from_fn"]
        is_snap_from_fn       get_snap_from_fn
    fn Snapshot::inner         ["snapshot_inner"]
        is_snap_inner         get_snap_inner
    fn Snapshot::deref         ["snapshot_deref"]
        is_snapshot_deref     get_snapshot_deref
    fn GhostBox::new           ["ghost_box_new"]
        is_ghost_new          get_ghost_new
    fn GhostBox::from_fn       ["ghost_from_fn"]
        is_ghost_from_fn      get_ghost_from_fn
    fn GhostBox::into_inner    ["ghost_box_into_inner"]
        is_ghost_into_inner   get_ghost_into_inner
    fn GhostBox::inner_logic   ["ghost_box_inner_logic"]
        is_ghost_inner_logic  get_ghost_inner_logic
    fn IndexLogic::index_logic ["index_logic_method"]
        is_index_logic        get_index_logic
    type Int                   ["creusot_int"]
        is_int_ty             get_int_ty
    type Snapshot              ["snapshot_ty"]
        is_snap_def_id        get_snap_ty
    type GhostBox              ["ghost_box"]
        is_ghost_ty           get_ghost_ty
}

/// Check if `ty` is the `Snapshot` type
pub(crate) fn is_snap_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let Some(adt) = ty.ty_adt_def() else { return false };
    is_snap_def_id(tcx, adt.did())
}

//! Special symbols defined in [`creusot_contracts`] and annotated with
//! `#[rustc_diagnostic_item = "..."]`

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum AreContractsLoaded {
    Yes,
    No,
    MissingItems(Vec<String>),
}

macro_rules! contracts_items {
    (
        $(#[$std_items:meta])?
        {
            $(
                $kind:tt $name:path [ $symbol:literal ] $is_name:ident $get_name:ident
            )*
        }
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

        contracts_items! {
            @are_contracts_loaded
            $(#[$std_items])?
            $($symbol)*
        }
    };
    (@kind fn) => { "function" };
    (@kind type) => { "type" };
    (@are_contracts_loaded #[$std_items:meta] $($symbol:literal)*) => {};
    (@are_contracts_loaded $($symbol:literal)*) => {
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
}

contracts_items! {{
    fn inv                               ["creusot_invariant_internal"]
        is_inv_function                 get_inv_function
    fn resolve                           ["creusot_resolve"]
        is_resolve_function             get_resolve_function
    fn structural_resolve                ["creusot_structural_resolve"]
        is_structural_resolve           get_structural_resolve
    fn invariant                         ["creusot_invariant_user"]
        is_invariant_method             get_invariant_method
    fn resolve                           ["creusot_resolve_method"]
        is_resolve_method               get_resolve_method
    fn Snapshot::from_fn                 ["snapshot_from_fn"]
        is_snap_from_fn                 get_snap_from_fn
    fn Snapshot::deref                   ["snapshot_deref"]
        is_snapshot_deref               get_snapshot_deref
    fn Ghost::new                        ["ghost_new"]
        is_ghost_new                    get_ghost_new
    fn Ghost::into_inner                 ["ghost_into_inner"]
        is_ghost_into_inner             get_ghost_into_inner
    fn Ghost::inner_logic                ["ghost_inner_logic"]
        is_ghost_inner_logic            get_ghost_inner_logic
    fn Ghost::deref                      ["ghost_deref"]
        is_ghost_deref                  get_ghost_deref
    fn Ghost::deref_mut                  ["ghost_deref_mut"]
        is_ghost_deref_mut              get_ghost_deref_mut
    fn IndexLogic::index_logic           ["creusot_index_logic_method"]
        is_index_logic                  get_index_logic
    fn FnOnceExt::precondition           ["fn_once_impl_precond"]
        is_fn_once_impl_precond         get_fn_once_impl_precond
    fn FnOnceExt::postcondition_once     ["fn_once_impl_postcond"]
        is_fn_once_impl_postcond        get_fn_once_impl_postcond
    fn FnMutExt::postcondition_mut       ["fn_mut_impl_postcond"]
        is_fn_mut_impl_postcond         get_fn_mut_impl_postcond
    fn FnMutExt::hist_inv                  ["fn_mut_impl_hist_inv"]
        is_fn_mut_impl_hist_inv           get_fn_mut_impl_hist_inv
    fn Fn::postcondition                 ["fn_impl_postcond"]
        is_fn_impl_postcond             get_fn_impl_postcond
    type Int                             ["creusot_int"]
        is_int_ty                       get_int_ty
    type Snapshot                        ["snapshot_ty"]
        is_snap_ty                      get_snap_ty
    type Ghost                           ["ghost_ty"]
        is_ghost_ty                     get_ghost_ty
}}

contracts_items! { #[std_items] {
    fn Deref::deref                      ["deref_method"]
        is_deref                        get_deref
    fn Deref::deref_mut                  ["deref_mut_method"]
        is_deref_mut                    get_deref_mut
    fn Box::new                          ["box_new"]
        is_box_new                      get_box_new
}}

use crate::*;

/// Raw pointer whose ownership is tracked by a ghost [PtrOwn].
pub type RawPtr<T> = *const T;

/// Token that represents the ownership of a memory cell. A [PtrOwn] value only
/// exists in the ghost world, but can be used in combination with a
/// corresponding [RawPtr] to access and modify memory.
///
/// A warning regarding memory leaks: dropping a `GhostBox<PtrOwn<T>>` (we only
/// ever handle ghost [PtrOwn] values) cannot deallocate the memory
/// corresponding to the pointer because it is a ghost value. One must thus
/// remember to explicitly call [drop] in order to free the memory tracked by a
/// [PtrOwn] token.
pub struct PtrOwn<T: ?Sized> {
    pub ptr: RawPtr<T>,
    pub val: T,
}

impl<T: ?Sized> Invariant for PtrOwn<T> {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { !self.ptr.is_null_logic() && inv(self.val) }
    }
}

/// Creates a new [PtrOwn] and associated [RawPtr] by allocating a new memory
/// cell initialized with `v`.
#[ensures(result.1.ptr == result.0 && result.1.val == v)]
pub fn new<T>(v: T) -> (RawPtr<T>, GhostBox<PtrOwn<T>>) {
    from_box(Box::new(v))
}

/// Creates a ghost [PtrOwn] and associated [RawPtr] from an existing [Box].
#[trusted]
#[ensures(result.1.ptr == result.0 && result.1.val == *val)]
pub fn from_box<T: ?Sized>(val: Box<T>) -> (RawPtr<T>, GhostBox<PtrOwn<T>>) {
    assert!(
        core::mem::size_of_val::<T>(&*val) > 0,
        "PtrOwn doesn't support ZSTs"
    );
    (
        Box::into_raw(val),
        GhostBox::conjure(),
    )
}

/// Immutably borrows the underlying `T`.
#[trusted]
#[requires(ptr == own.ptr)]
#[ensures(*result == own.val)]
#[allow(unused_variables)]
pub fn as_ref<T: ?Sized>(ptr: RawPtr<T>, own: GhostBox<&PtrOwn<T>>) -> &T {
    unsafe { &*ptr }
}

/// Mutably borrows the underlying `T`.
#[trusted]
#[allow(unused_variables)]
#[requires(ptr == own.ptr)]
#[ensures(*result == own.val)]
// TODO: why is .inner_logic() needed instead of *?
// #[ensures((^*own).ptr == own.ptr)] raises the error:
// error: unsupported logical reborrow UpvarRef { closure_def_id: DefId(0:5333 ~ creusot_contracts[0c6a]::ptr_own::as_mut::{closure#1}), var_hir_id: LocalVarId(HirId(DefId(0:5330 ~ creusot_contracts[0c6a]::ptr_own::as_mut).4)) }, only field projections and slice indexing are supported
//   --> creusot-contracts/src/ptr_own.rs:72:14
//    |
// 72 | #[ensures((^*own).ptr == own.ptr)]
//    |              ^^^
#[ensures((^own.inner_logic()).ptr == own.ptr)]
#[ensures((^own.inner_logic()).val == ^result)]
pub fn as_mut<T: ?Sized>(ptr: RawPtr<T>, own: GhostBox<&mut PtrOwn<T>>) -> &mut T {
    unsafe { &mut *(ptr as *mut _) }
}

/// Transfers ownership of `own` back into a [Box].
#[trusted]
#[requires(ptr == own.ptr)]
#[ensures(*result == own.val)]
#[allow(unused_variables)]
pub fn to_box<T: ?Sized>(ptr: RawPtr<T>, own: GhostBox<PtrOwn<T>>) -> Box<T> {
    unsafe { Box::from_raw(ptr as *mut _) }
}

/// Deallocates the memory pointed by `ptr`.
#[requires(ptr == own.ptr)]
pub fn drop<T: ?Sized>(ptr: RawPtr<T>, own: GhostBox<PtrOwn<T>>) {
    let _ = to_box(ptr, own);
}

/// If one owns two [PtrOwn]s in ghost code, then they are for different pointers.
#[trusted]
#[ensures(own1.ptr != own2.ptr)]
#[ensures(own1.ptr.addr_logic() != own2.ptr.addr_logic())]
#[allow(unused_variables)]
pub fn disjoint_lemma<T: ?Sized>(own1: &mut PtrOwn<T>, own2: &mut PtrOwn<T>) {
    panic!()
}

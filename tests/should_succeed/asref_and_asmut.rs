extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(<T as AsRef<[u8]>>::as_ref.precondition((&bytes,)))]
#[ensures(exists<s: &[u8]>
    <T as AsRef<[u8]>>::as_ref.postcondition((&bytes,), s) &&
    result@ == s@.len()
)]
pub fn get_len_through_as_ref<T: AsRef<[u8]>>(bytes: T) -> usize {
    bytes.as_ref().len()
}

#[ensures(result@ == bytes@.len())]
pub fn get_len_of_slice(bytes: &[u8]) -> usize {
    get_len_through_as_ref(bytes)
}

/*
// Creusot does not support reborrowing with "&mut" in Pearlite
#[ensures(exists<s: &mut [u8]>
    <T as AsMut<[u8]>>::as_mut.postcondition((&mut bytes,), s) &&
    result@ == s@.len()
)]
pub fn get_len_through_as_mut<T: AsMut<[u8]>>(mut bytes: T) -> usize {
    bytes.as_mut().len()
}
*/

#[ensures(result@ == bytes@.len())]
pub fn get_len_of_mut_slice(bytes: &mut [u8]) -> usize {
    <[u8] as AsMut<[u8]>>::as_mut(bytes).len()
}

#[ensures(result@ == bytes@.len())]
pub fn get_len_of_mut_slice_with_ref_mut(mut bytes: &mut [u8]) -> usize {
    <&mut [u8] as AsMut<[u8]>>::as_mut(&mut bytes).len()
}

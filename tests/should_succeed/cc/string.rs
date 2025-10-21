extern crate creusot_contracts;
use creusot_contracts::{logic::seq::flat_map_singleton, prelude::*};

#[requires(s@ == seq!['Ã'])]
#[requires('Ã'.to_utf8() == seq![0xC3u8, 0x83u8])]
#[ensures(result@ == 2)]
pub fn test_string_len(s: String) -> usize {
    s.len()
}

#[requires(s@ == seq!['Ã'])]
#[requires('Ã'.to_utf8() == seq![0xC3u8, 0x83u8])]
#[ensures(result@ == 2)]
pub fn test_str_len(s: &str) -> usize {
    s.len()
}

#[requires(s@ == seq!['Ã'])]
#[requires('Ã'.to_utf8() == seq![0xC3u8, 0x83u8])]
#[ensures(result.0@ == s@ && result.1@ == Seq::empty())]
pub fn test_split_at(s: &str) -> (&str, &str) {
    snapshot! { flat_map_singleton::<char, u8>() };
    proof_assert! { s@.subsequence(0, 1) == s@ };
    s.split_at(2)
}

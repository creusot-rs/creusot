extern crate creusot_std;

use creusot_std::{cell::PredCell, logic::Mapping, prelude::*};

#[requires(forall<s: &[u32]> cell@[*s] == (s@.len() == 2 && s[0]@ % 2 == 0 && s[1]@ % 2 == 1))]
#[ensures(result.0@ % 2 == 0 && result.1@ % 2 == 1)]
pub fn splits_up(cell: &PredCell<[u32]>) -> (u32, u32) {
    let snapshot: Snapshot<Seq<Mapping<u32, bool>>> = snapshot! {
        let pred0 = |z: u32| z@ % 2 == 0;
        let pred1 = |z: u32| z@ % 2 == 1;
        seq!(pred0, pred1)
    };

    let slice = cell.as_slice_of_cells(snapshot);
    (slice[0].get(), slice[1].get())
}

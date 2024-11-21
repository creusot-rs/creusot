extern crate creusot_contracts;

pub fn char_match_bad(x: char) {
    match x {
        'a' => (),
        _ => (),
    }
}

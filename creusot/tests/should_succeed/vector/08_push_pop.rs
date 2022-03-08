// WHY3PROVE Z3
extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;


fn vec_push_pop<T>(v: &mut Vec<T>, e: T) {
    let old_v = Ghost::record(&v);

    v.push(e);
    let r = v.pop();

    match r {
      Some(v) => (),
      None => (),
    };

    proof_assert!(@v == @@old_v);
    // Unprovable (automatically at least) without the previous line
    proof_assert!(@v === @@old_v);
}
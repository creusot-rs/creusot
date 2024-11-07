extern crate creusot_contracts;
use creusot_contracts::*;

#[expect(creusot::experimental)]
pub fn f() {
    print!("Hello ");
    println!("world!");
    eprint!("Hello ");
    eprintln!("stderr!");

    proof_assert!(1 + 1 == 2); // So we have something to prove

    // FIXME: not supported at the moment
    // print!("{} ", "Hello");
    // println!("{}!", "world");
    // eprint!("{} ", "Hello");
    // eprintln!("{}!", "stderr");
}

extern crate creusot_std;
use creusot_std::prelude::*;

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

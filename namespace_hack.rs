#![feature(decl_macro)]
extern crate creusot_contracts_proc;

use creusot_contracts_proc::*;

// #[custom_namespace(unique_ident!())]
// fn my_func() {

// }
//
unique_ident!();

def_site!();
// __custom_namespaced__! {
//   fn something_logical() {

//   }
// }

// __custom_namespaced__! {
//   fn other_thing() {
//     something_logical()
//   }
// }
//
test_gen!();

__test2__!();

// __test2__!();


#[custom_namespace]
fn something() { }

#[custom_namespace]
fn something2() {
  // something()
}

// mod abc {
// __custom_namespaced__! {
//   fn other_logic() { }
// }
// }


fn program() {
  // predicate()
}

fn main () { }
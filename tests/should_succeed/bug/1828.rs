extern crate creusot_std;

// Prevent reintroducing bug described in issue:
// https://github.com/creusot-rs/creusot/issues/1828
pub fn foo<S>(_: &S) -> impl Fn() -> u64 {
    move || 0
}

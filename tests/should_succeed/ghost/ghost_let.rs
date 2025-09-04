extern crate creusot_contracts;
use creusot_contracts::*;

pub struct WithInv(i32);

impl Invariant for WithInv {
    #[logic]
    fn invariant(self) -> bool {
        self.0 == 1i32
    }
}

#[requires(true)]
pub fn foo(g: Ghost<&mut WithInv>) {
    // reborrow the inner structure, with no type invariant
    ghost_let!(g2 = &mut g.into_inner().0);

    bar(g2);
}

#[ensures((^*g2) == 1i32)]
fn bar(mut g2: Ghost<&mut i32>) {
    ghost! {
        **g2 = 1;
    };
}

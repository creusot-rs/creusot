extern crate creusot_contracts;
use creusot_contracts::*;

struct NonCopy(i32);
impl View for NonCopy {
    type ViewTy = Int;
    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        pearlite! { self.0@ }
    }
}

pub fn ghost_enter_ghost() {
    let g_move = ghost!(NonCopy(1));
    let g_read = ghost!(NonCopy(2));
    let mut g_mut = ghost!(NonCopy(3));

    ghost! {
        let _ = g_move;
        let _ = g_read.0;
        *g_mut = NonCopy(4);
    };

    proof_assert!(g_read@ == 2);
    proof_assert!(g_mut@ == 4);
}

pub fn snapshot_enter_ghost() {
    let g_read = snapshot!(NonCopy(1i32));
    let mut g_mut;

    ghost! {
        let _ = g_read;
        g_mut = snapshot!(NonCopy(3i32));
        proof_assert!(g_mut@ == 3);
        g_mut = snapshot!(NonCopy(4i32));
    };

    proof_assert!(g_read@ == 1);
    proof_assert!(g_mut@ == 4);
}

pub fn copy_enter_ghost() {
    let x = 2i32;
    let unit = ();
    let pair = (6, 42);

    ghost! {
        let _x = x;
        let _unit = unit;
        let _pair = pair;
    };
    proof_assert!(x@ == 2);
    proof_assert!(pair.0@ == 6 && pair.1@ == 42);
}

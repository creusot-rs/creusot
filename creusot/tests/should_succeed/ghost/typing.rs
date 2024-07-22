extern crate creusot_contracts;
use creusot_contracts::*;

struct NonCopy(i32);
impl ShallowModel for NonCopy {
    type ShallowModelTy = Int;
    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { self.0@ }
    }
}

pub fn ghost_enter_ghost() {
    let g_move = gh!(NonCopy(1));
    let g_read = gh!(NonCopy(2));
    let mut g_mut = gh!(NonCopy(3));

    ghost! {
        let _ = g_move;
        let _ = g_read.0;
        *g_mut = NonCopy(4);
    }

    proof_assert!(g_read@ == 2);
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
    }
    proof_assert!(x@ == 2);
    proof_assert!(pair.0@ == 6 && pair.1@ == 42);
}

pub fn exit_ghost() {
    let _unit: () = ghost! {};

    let g1 = ghost! { GhostBox::new(5) };
    let g2 = gh!(5);
    proof_assert!(g1@ + g2@ == 10);
}

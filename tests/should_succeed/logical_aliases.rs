extern crate creusot_contracts;
use creusot_contracts::*;

#[has_logical_alias(add_logic)]
#[check(ghost)]
fn add(x: Int, y: Int) -> Int {
    x + y
}
#[logic]
fn add_logic(x: Int, y: Int) -> Int {
    x + y
}

pub fn test_add() {
    ghost! {
       let x = 3int;
       let y = add(x, 5int);
       proof_assert!(y == add(x, 5));
    };
}

struct Seq2<T>(Seq<T>);

impl<T> Seq2<T> {
    #[has_logical_alias(Self::len_logic)]
    #[check(ghost)]
    fn len(&self) -> Int {
        self.0.len_ghost()
    }
    #[logic]
    fn len_logic(&self) -> Int {
        self.0.len()
    }
}

pub fn test_seq() {
    ghost! {
        let mut s = Seq2(Seq::new().into_inner());
        s.0.push_back_ghost(2int);
        let l1 = s.len();
        proof_assert!(l1 == s.len());
        s.0.push_back_ghost(4int);
        let l2 = s.len();
        proof_assert!(l2 == s.len());
    };
}

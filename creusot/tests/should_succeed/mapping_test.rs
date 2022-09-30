// basic tests for mappings

extern crate creusot_contracts;
use creusot_contracts::*;

struct T {
    a: i32,
}

impl ShallowModel for T {
    type ShallowModelTy = Mapping<Int, Int>;

    #[logic]
    #[trusted]
    #[ensures(
        forall<i:Int>
            result.get(i) == (if 0 <= i && i < @self.a { 1 } else { 0 }))]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

#[requires( 0 <= @(*t).a )] // otherwise its wrong !
#[requires( @(*t).a < 1000 )] // to prevent overflow
#[ensures( @^t == (@t).set(@(*t).a,1) )]
fn incr(t: &mut T) {
    let old_t = ghost! { t };
    (*t).a += 1;
    // proving the post-consition via extensional equality of mappings
    // (notice `==` versus `==`)
    proof_assert!( @^t == (@old_t).set(@old_t.a,1) );
}

pub fn f() {
    let mut x = T { a: 42 };
    proof_assert!( (@x).get(13) == 1 );
    proof_assert!( (@x).get(42) == 0 );
    incr(&mut x);
    proof_assert!( (@x).get(13) == 1 );
    proof_assert!( (@x).get(42) == 1 );
}

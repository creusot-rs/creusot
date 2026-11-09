use creusot_std::prelude::*;

pub mod private {
    use super::*;

    #[logic(open(self))]
    pub fn gen_key(seed: Int) -> Int {
        let _ = seed;
        4
    }

    #[logic(open(self))]
    pub fn is_secure(pkey: Int) -> bool {
        let _ = pkey;
        true
    }

    #[logic]
    #[ensures(
        #[trigger(gen_key(seed))]
        is_secure(gen_key(seed))
    )]
    pub fn lemma_all_good(seed: Int) {
        let _ = seed;
    }
}

#[logic(opaque)]
pub fn rng_seed() -> Int {
    dead
}

#[import(private::lemma_all_good)]
pub mod direct {
    use super::*;

    #[logic]
    #[ensures(private::is_secure(private::gen_key(rng_seed())))]
    pub fn all_good() {}
}

pub trait Axiom {
    #[logic(law)]
    #[ensures(
        #[trigger(private::gen_key(seed))]
        private::is_secure(private::gen_key(seed))
    )]
    fn lemma_all_good(seed: Int) {
        private::lemma_all_good(seed);
    }

    #[logic]
    fn assoc() {}
}
impl<T> Axiom for T {}

#[import(<()>::assoc)]
pub mod law {
    use super::*;

    #[logic]
    #[ensures(private::is_secure(private::gen_key(rng_seed())))]
    pub fn all_good() {}
}

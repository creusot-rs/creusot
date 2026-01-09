extern crate creusot_std;
use creusot_std::prelude::*;
pub fn test() {
    let c = {
        #[requires(x@ < 1000)]
        #[ensures(result@ == x@ + 1)]
        |x: usize| x + 1
    };
    let y = c(2);
    proof_assert!(y@ == 3)
}

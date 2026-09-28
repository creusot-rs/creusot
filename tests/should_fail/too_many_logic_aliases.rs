use creusot_std::prelude::*;

#[logic]
pub fn logic1(x: u32) -> bool {
    let _ = x;
    true
}

#[logic]
pub fn logic2(x: u32) -> bool {
    let _ = x;
    true
}

#[logic_alias(logic1)]
#[logic_alias(logic2)]
pub fn hybrid(x: u32) -> bool {
    let _ = x;
    false
}

#[logic]
pub fn test(x: u32) {
    hybrid(x);
}

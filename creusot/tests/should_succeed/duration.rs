extern crate creusot_contracts;

use creusot_contracts::*;

use std::time::Duration;

pub fn test_duration() {
    let zero = Duration::new(0, 0);
    proof_assert!(zero@ == 0);
    assert!(zero.as_nanos() == 0);

    let max = Duration::new(u64::MAX, 999_999_999);

    let d_secs = Duration::from_secs(1);
    proof_assert!(d_secs@ == 1_000_000_000);

    let d_millis = Duration::from_millis(1);
    proof_assert!(d_millis@ == 1_000_000);

    let d_micros = Duration::from_micros(1);
    proof_assert!(d_micros@ == 1_000);

    let d_nanos = Duration::from_nanos(1);
    proof_assert!(d_nanos@ == 1);

    assert!(zero.is_zero());
    assert!(!d_secs.is_zero());

    assert!(1 == d_secs.as_secs());
    assert!(0 == d_secs.subsec_millis());
    assert!(0 == d_secs.subsec_micros());
    assert!(0 == d_secs.subsec_nanos());

    assert!(d_millis.subsec_millis() as u128 == d_millis.as_millis());
    assert!(d_micros.subsec_micros() as u128 == d_micros.as_micros());
    assert!(d_nanos.subsec_nanos() as u128 == d_nanos.as_nanos());

    assert!(d_secs.checked_add(max).is_none());
    assert!(d_secs.checked_add(d_secs).is_some());

    assert!(d_secs.checked_sub(max).is_none());
    assert!(d_secs.checked_sub(d_millis).is_some());

    assert!(max.checked_mul(2).is_none());
    assert!(d_secs.checked_mul(10).is_some());

    assert!(d_secs.checked_div(0).is_none());
    assert!(d_secs.checked_div(10).is_some());

    let sum = d_millis + d_micros;
    let difference = d_millis - d_micros;
    proof_assert!(sum@ == 1_001_000);
    proof_assert!(difference@ == 999000);
}

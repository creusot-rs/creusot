extern crate creusot_std;

use creusot_std::prelude::*;

use std::time::{Duration, Instant};

pub fn test_instant() {
    let instant = Instant::now();
    let zero_dur = Duration::from_secs(0);
    assert!(instant.elapsed() >= zero_dur);

    assert!(instant.checked_add(zero_dur).unwrap() == instant);
    assert!(instant + zero_dur == instant);
    let three_seconds = Duration::from_secs(3);
    let greater_instant = instant + three_seconds;
    proof_assert!(instant@ < greater_instant@);
    let even_greater_instant = greater_instant + three_seconds;
    proof_assert!(instant@ < even_greater_instant@);

    assert!(instant.checked_sub(zero_dur).unwrap() == instant);
    assert!(instant - zero_dur == instant);
    let lesser_instant = instant - three_seconds;
    proof_assert!(instant@ > lesser_instant@);
    assert!(instant - instant == zero_dur);
    assert!(instant - greater_instant == zero_dur);
    assert!(greater_instant - instant > zero_dur);

    assert!(greater_instant.duration_since(instant) > zero_dur);
    assert!(instant.duration_since(greater_instant) == zero_dur);
    assert!(greater_instant.checked_duration_since(instant).is_some());
    assert!(instant.checked_duration_since(greater_instant).is_none());
    assert!(greater_instant.saturating_duration_since(instant) > zero_dur);
    assert!(instant.saturating_duration_since(greater_instant) == zero_dur);
}

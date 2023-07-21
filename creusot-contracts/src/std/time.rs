use crate::*;
pub use ::std::{
    ops::{Add, Sub},
    time::*,
};

impl ShallowModel for Duration {
    type ShallowModelTy = Int;

    #[ghost]
    #[open(self)]
    #[trusted]
    #[ensures(result >= 0 && result <= secs_to_nanos(u64::MAX@) + 999_999_999)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { absurd }
    }
}

impl DeepModel for Duration {
    type DeepModelTy = Int;

    #[ghost]
    #[open(self)]
    #[trusted]
    #[ensures(result >= 0 && result <= secs_to_nanos(u64::MAX@) + 999_999_999)]
    #[ensures(result == self.shallow_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { absurd }
    }
}

#[ghost]
fn nanos_to_micros(nanos: Int) -> Int {
    nanos / 1_000
}
#[ghost]
fn nanos_to_millis(nanos: Int) -> Int {
    nanos / 1_000_000
}

#[ghost]
fn nanos_to_secs(nanos: Int) -> Int {
    nanos / 1_000_000_000
}

#[ghost]
fn secs_to_nanos(secs: Int) -> Int {
    secs * 1_000_000_000
}

impl ShallowModel for Instant {
    type ShallowModelTy = Int;

    #[ghost]
    #[open(self)]
    #[trusted]
    #[ensures(result >= 0)]
    fn shallow_model(self) -> Self::ShallowModelTy {
        pearlite! { absurd }
    }
}

impl DeepModel for Instant {
    type DeepModelTy = Int;

    #[ghost]
    #[open(self)]
    #[trusted]
    #[ensures(result >= 0)]
    #[ensures(result == self.shallow_model())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { absurd }
    }
}

extern_spec! {
    mod std {
        mod time {
            impl Duration {
                #[requires(secs@ + nanos_to_secs(nanos@) <= u64::MAX@)]
                #[ensures(result@ == secs_to_nanos(secs@) + nanos@ )]
                fn new(secs: u64, nanos: u32) -> Duration;

                #[ensures(result@ == secs_to_nanos(secs@))]
                fn from_secs(secs: u64) -> Duration;

                #[ensures(result@ == (millis@ * 1_000_000))]
                fn from_millis(millis: u64) -> Duration;

                #[ensures(result@ == (micros@ * 1_000))]
                fn from_micros(micros: u64) -> Duration;

                #[ensures(result@ == nanos@)]
                fn from_nanos(nanos: u64) -> Duration;

                #[ensures(self@ == 0 ==> result == true)]
                #[ensures(self@ != 0 ==> result == false)]
                fn is_zero(&self) -> bool;

                #[ensures(result@ == nanos_to_secs(self@))]
                fn as_secs(&self) -> u64;

                #[ensures(result@ == nanos_to_millis(self@) % 1_000)]
                #[ensures(result < 1_000_u32)]
                fn subsec_millis(&self) -> u32;

                #[ensures(result@ == nanos_to_micros(self@) % 1_000_000)]
                #[ensures(result < 1_000_000_u32)]
                fn subsec_micros(&self) -> u32;

                #[ensures(result@ == (self@ % 1_000_000_000))]
                #[ensures(result < 1_000_000_000_u32)]
                fn subsec_nanos(&self) -> u32;

                #[ensures(result@ == nanos_to_millis(self@))]
                fn as_millis(&self) -> u128;

                #[ensures(result@ == nanos_to_micros(self@))]
                fn as_micros(&self) -> u128;

                #[ensures(result@ == self@)]
                #[ensures(result@ <= secs_to_nanos(u64::MAX@) + 999_999_999)]
                fn as_nanos(&self) -> u128;

                #[ensures(nanos_to_secs(self@ + rhs@) > u64::MAX@ ==> result == None)]
                #[ensures(nanos_to_secs(self@ + rhs@) <= u64::MAX@ ==> result.deep_model() == Some(self@ + rhs@))]
                fn checked_add(self, rhs: Duration) -> Option<Duration>;

                #[ensures(self@ - rhs@ < 0 ==> result == None)]
                #[ensures(self@ - rhs@ >= 0 ==> result.deep_model() == Some(self@ - rhs@))]
                fn checked_sub(self, rhs: Duration) -> Option<Duration>;

                #[ensures(nanos_to_secs(self@ * rhs@) > u64::MAX@ ==> result == None)]
                #[ensures(nanos_to_secs(self@ * rhs@) <= u64::MAX@ ==> result.deep_model() == Some(self@ * rhs@))]
                fn checked_mul(self, rhs: u32) -> Option<Duration>;

                #[ensures(rhs == 0u32 ==> result == None)]
                #[ensures(rhs != 0u32 ==> result.deep_model() == Some(self@ / rhs@))]
                fn checked_div(self, rhs: u32) -> Option<Duration>;
            }

            impl Instant {
                #[ensures(result@ >= 0)]
                fn now() -> Instant;

                #[ensures(result@ >= 0)]
                fn elapsed(&self) -> Duration;

                #[ensures(self@ > earlier@ ==> result@ > 0)]
                #[ensures(self@ <= earlier@ ==> result@ == 0)]
                fn duration_since(&self, earlier: Instant) -> Duration;

                #[ensures(self@ >= earlier@ ==> result != None)]
                #[ensures(self@ < earlier@ ==> result == None)]
                fn checked_duration_since(&self, earlier: Instant) -> Option<Duration>;

                #[ensures(self@ > earlier@ ==> result@ > 0)]
                #[ensures(self@ <= earlier@ ==> result@ == 0)]
                fn saturating_duration_since(&self, earlier: Instant) -> Duration;

                #[ensures(duration@ == 0 ==> result.deep_model() == Some(self@))]
                #[ensures(duration@ > 0 && result != None ==> Some(self@) < result.deep_model())]
                fn checked_add(&self, duration: Duration) -> Option<Instant>;

                #[ensures(duration@ == 0 ==> result.deep_model() == Some(self@))]
                #[ensures(duration@ > 0 && result != None ==> Some(self@) > result.deep_model())]
                fn checked_sub(&self, duration: Duration) -> Option<Instant>;
            }
        }
    }
}

extern_spec! {
    impl Add<Duration> for Duration {
        #[requires(self@ + rhs@ <= secs_to_nanos(u64::MAX@) + 999_999_999)]
        #[ensures(self@ + rhs@ == result@)]
        fn add(self, rhs: Duration) -> Duration;
    }

    impl Sub<Duration> for Duration {
        #[requires(self@ - rhs@ >= 0)]
        #[ensures(self@ - rhs@ == result@)]
        fn sub(self, rhs: Duration) -> Duration;
    }

    impl Add<Duration> for Instant {
        #[ensures(rhs@ == 0 ==> self@ == result@)]
        #[ensures(rhs@ > 0 ==> self@ < result@)]
        fn add(self, rhs: Duration) -> Instant;
    }

    impl Sub<Duration> for Instant {
        #[ensures(rhs@ == 0 ==> self@ == result@)]
        #[ensures(rhs@ > 0 ==> self@ > result@)]
        fn sub(self, rhs: Duration) -> Instant;
    }

    impl Sub<Instant> for Instant {
        #[ensures(self@ > other@ ==> result@ > 0)]
        #[ensures(self@ <= other@ ==> result@ == 0)]
        fn sub(self, other: Instant) -> Duration;
    }
}

use crate::*;
pub use ::std::{
    ops::{Add, Sub},
    time::*,
};

impl View for Duration {
    type ViewTy = Int;

    #[trusted]
    #[logic(opaque)]
    #[ensures(result >= 0 && result <= secs_to_nanos(u64::MAX@) + 999_999_999)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl DeepModel for Duration {
    type DeepModelTy = Int;

    #[logic(open)]
    fn deep_model(self) -> Self::DeepModelTy {
        self.view()
    }
}

#[logic(open)]
pub fn nanos_to_micros(nanos: Int) -> Int {
    nanos / 1_000
}
#[logic(open)]
pub fn nanos_to_millis(nanos: Int) -> Int {
    nanos / 1_000_000
}

#[logic(open)]
pub fn nanos_to_secs(nanos: Int) -> Int {
    nanos / 1_000_000_000
}

#[logic(open)]
pub fn secs_to_nanos(secs: Int) -> Int {
    secs * 1_000_000_000
}

impl View for Instant {
    type ViewTy = Int;

    #[trusted]
    #[logic(opaque)]
    #[ensures(result >= 0)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl DeepModel for Instant {
    type DeepModelTy = Int;

    #[logic(open)]
    fn deep_model(self) -> Self::DeepModelTy {
        self.view()
    }
}

extern_spec! {
    mod std {
        mod time {
            impl Duration {
                #[check(ghost)]
                #[requires(secs@ + nanos_to_secs(nanos@) <= u64::MAX@)]
                #[ensures(result@ == secs_to_nanos(secs@) + nanos@ )]
                fn new(secs: u64, nanos: u32) -> Duration;

                #[check(ghost)]
                #[ensures(result@ == secs_to_nanos(secs@))]
                fn from_secs(secs: u64) -> Duration;

                #[check(ghost)]
                #[ensures(result@ == (millis@ * 1_000_000))]
                fn from_millis(millis: u64) -> Duration;

                #[check(ghost)]
                #[ensures(result@ == (micros@ * 1_000))]
                fn from_micros(micros: u64) -> Duration;

                #[check(ghost)]
                #[ensures(result@ == nanos@)]
                fn from_nanos(nanos: u64) -> Duration;

                #[check(ghost)]
                #[ensures(self@ == 0 ==> result == true)]
                #[ensures(self@ != 0 ==> result == false)]
                fn is_zero(&self) -> bool;

                #[check(ghost)]
                #[ensures(result@ == nanos_to_secs(self@))]
                fn as_secs(&self) -> u64;

                #[check(ghost)]
                #[ensures(result@ == nanos_to_millis(self@) % 1_000)]
                #[ensures(result < 1_000_u32)]
                fn subsec_millis(&self) -> u32;

                #[check(ghost)]
                #[ensures(result@ == nanos_to_micros(self@) % 1_000_000)]
                #[ensures(result < 1_000_000_u32)]
                fn subsec_micros(&self) -> u32;

                #[check(ghost)]
                #[ensures(result@ == (self@ % 1_000_000_000))]
                #[ensures(result < 1_000_000_000_u32)]
                fn subsec_nanos(&self) -> u32;

                #[check(ghost)]
                #[ensures(result@ == nanos_to_millis(self@))]
                fn as_millis(&self) -> u128;

                #[check(ghost)]
                #[ensures(result@ == nanos_to_micros(self@))]
                fn as_micros(&self) -> u128;

                #[check(ghost)]
                #[ensures(result@ == self@)]
                #[ensures(result@ <= secs_to_nanos(u64::MAX@) + 999_999_999)]
                fn as_nanos(&self) -> u128;

                #[check(ghost)]
                #[ensures(nanos_to_secs(self@ + rhs@) > u64::MAX@ ==> result == None)]
                #[ensures(nanos_to_secs(self@ + rhs@) <= u64::MAX@ ==> result.deep_model() == Some(self@ + rhs@))]
                fn checked_add(self, rhs: Duration) -> Option<Duration>;

                #[check(ghost)]
                #[ensures(self@ - rhs@ < 0 ==> result == None)]
                #[ensures(self@ - rhs@ >= 0 ==> result.deep_model() == Some(self@ - rhs@))]
                fn checked_sub(self, rhs: Duration) -> Option<Duration>;

                #[check(ghost)]
                #[ensures(nanos_to_secs(self@ * rhs@) > u64::MAX@ ==> result == None)]
                #[ensures(nanos_to_secs(self@ * rhs@) <= u64::MAX@ ==> result.deep_model() == Some(self@ * rhs@))]
                fn checked_mul(self, rhs: u32) -> Option<Duration>;

                #[check(ghost)]
                #[ensures(rhs == 0u32 ==> result == None)]
                #[ensures(rhs != 0u32 ==> result.deep_model() == Some(self@ / rhs@))]
                fn checked_div(self, rhs: u32) -> Option<Duration>;
            }

            impl Instant {
                #[ensures(result@ >= 0)]
                fn now() -> Instant;

                #[ensures(result@ >= 0)]
                fn elapsed(&self) -> Duration;

                #[check(ghost)]
                #[ensures(self@ > earlier@ ==> result@ > 0)]
                #[ensures(self@ <= earlier@ ==> result@ == 0)]
                fn duration_since(&self, earlier: Instant) -> Duration;

                #[check(ghost)]
                #[ensures(self@ >= earlier@ ==> result != None)]
                #[ensures(self@ < earlier@ ==> result == None)]
                fn checked_duration_since(&self, earlier: Instant) -> Option<Duration>;

                #[check(ghost)]
                #[ensures(self@ > earlier@ ==> result@ > 0)]
                #[ensures(self@ <= earlier@ ==> result@ == 0)]
                fn saturating_duration_since(&self, earlier: Instant) -> Duration;

                #[check(ghost)]
                #[ensures(duration@ == 0 ==> result.deep_model() == Some(self@))]
                #[ensures(duration@ > 0 && result != None ==> Some(self@) < result.deep_model())]
                fn checked_add(&self, duration: Duration) -> Option<Instant>;

                #[check(ghost)]
                #[ensures(duration@ == 0 ==> result.deep_model() == Some(self@))]
                #[ensures(duration@ > 0 && result != None ==> Some(self@) > result.deep_model())]
                fn checked_sub(&self, duration: Duration) -> Option<Instant>;
            }
        }
    }
}

extern_spec! {
    impl Add<Duration> for Duration {
        #[check(ghost)]
        #[requires(self@ + rhs@ <= secs_to_nanos(u64::MAX@) + 999_999_999)]
        #[ensures(self@ + rhs@ == result@)]
        fn add(self, rhs: Duration) -> Duration;
    }

    impl Sub<Duration> for Duration {
        #[check(ghost)]
        #[requires(self@ - rhs@ >= 0)]
        #[ensures(self@ - rhs@ == result@)]
        fn sub(self, rhs: Duration) -> Duration;
    }

    impl Add<Duration> for Instant {
        #[check(ghost)]
        #[ensures(rhs@ == 0 ==> self@ == result@)]
        #[ensures(rhs@ > 0 ==> self@ < result@)]
        fn add(self, rhs: Duration) -> Instant;
    }

    impl Sub<Duration> for Instant {
        #[check(ghost)]
        #[ensures(rhs@ == 0 ==> self@ == result@)]
        #[ensures(rhs@ > 0 ==> self@ > result@)]
        fn sub(self, rhs: Duration) -> Instant;
    }

    impl Sub<Instant> for Instant {
        #[check(ghost)]
        #[ensures(self@ > other@ ==> result@ > 0)]
        #[ensures(self@ <= other@ ==> result@ == 0)]
        fn sub(self, other: Instant) -> Duration;
    }
}

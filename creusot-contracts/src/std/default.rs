use creusot_contracts_proc::*;
use std::default::Default;

pub trait DefaultSpec: Default {
    #[logic]
    fn default_log() -> Self;
}

// TODO use a macro to factorize all this
// (macros need to be updated)

impl DefaultSpec for () {
    #[logic]
    fn default_log() -> () {
        ()
    }
}

impl DefaultSpec for bool {
    #[logic]
    fn default_log() -> bool {
        false
    }
}

impl DefaultSpec for usize {
    #[logic]
    fn default_log() -> usize {
        0usize
    }
}

impl DefaultSpec for isize {
    #[logic]
    fn default_log() -> isize {
        0isize
    }
}

impl DefaultSpec for u8 {
    #[logic]
    fn default_log() -> u8 {
        0u8
    }
}

impl DefaultSpec for i8 {
    #[logic]
    fn default_log() -> i8 {
        0i8
    }
}

impl DefaultSpec for u16 {
    #[logic]
    fn default_log() -> u16 {
        0u16
    }
}

impl DefaultSpec for i16 {
    #[logic]
    fn default_log() -> i16 {
        0i16
    }
}

impl DefaultSpec for u32 {
    #[logic]
    fn default_log() -> u32 {
        0u32
    }
}

impl DefaultSpec for i32 {
    #[logic]
    fn default_log() -> i32 {
        0i32
    }
}

impl DefaultSpec for u64 {
    #[logic]
    fn default_log() -> u64 {
        0u64
    }
}

impl DefaultSpec for i64 {
    #[logic]
    fn default_log() -> i64 {
        0i64
    }
}

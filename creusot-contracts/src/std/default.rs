use creusot_contracts_proc::*;

pub trait Default: std::default::Default {
    #[logic]
    fn default_log() -> Self;
}

// TODO use a macro to factorize all this
// (macros need to be updated)

impl Default for () {
    #[logic]
    fn default_log() -> () {
        ()
    }
}

impl Default for bool {
    #[logic]
    fn default_log() -> bool {
        false
    }
}

impl Default for usize {
    #[logic]
    fn default_log() -> usize {
        0usize
    }
}

impl Default for isize {
    #[logic]
    fn default_log() -> isize {
        0isize
    }
}

impl Default for u8 {
    #[logic]
    fn default_log() -> u8 {
        0u8
    }
}

impl Default for i8 {
    #[logic]
    fn default_log() -> i8 {
        0i8
    }
}

impl Default for u16 {
    #[logic]
    fn default_log() -> u16 {
        0u16
    }
}

impl Default for i16 {
    #[logic]
    fn default_log() -> i16 {
        0i16
    }
}

impl Default for u32 {
    #[logic]
    fn default_log() -> u32 {
        0u32
    }
}

impl Default for i32 {
    #[logic]
    fn default_log() -> i32 {
        0i32
    }
}

impl Default for u64 {
    #[logic]
    fn default_log() -> u64 {
        0u64
    }
}

impl Default for i64 {
    #[logic]
    fn default_log() -> i64 {
        0i64
    }
}

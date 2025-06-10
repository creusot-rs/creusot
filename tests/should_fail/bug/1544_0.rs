extern crate creusot_contracts;

// Should emit a readable error message, not a crash
pub fn unsupported_type(_x: &dyn std::fmt::Debug) {}

// SHOULD_SUCCEED: parse-print
#![feature(exclusive_range_pattern)]
// Test that matching constant integer values works
fn main() {
    match 1 {
        0..10 => {
            assert!(true)
        }
        5 | 6 => {
            assert!(false)
        }
        _ => {
            assert!(false)
        }
    }
}

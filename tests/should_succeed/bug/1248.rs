// Test for issue #1248: Wildcard patterns on integers are missing assumptions
// https://github.com/creusot-rs/creusot/issues/1248
//
// In integer match expressions, the default/wildcard branch should assume
// that the discriminant is NOT equal to any of the specific matched values.

extern crate creusot_std;

// Basic case from the issue - usize with single value
pub fn single_value_usize(x: usize) {
    match x {
        1 => assert!(x == 1),
        _ => assert!(x != 1),
    }
}

// Multiple values - should assume x != 1 && x != 2 && x != 3
pub fn multiple_values_usize(x: usize) {
    match x {
        1 => assert!(x == 1),
        2 => assert!(x == 2),
        3 => assert!(x == 3),
        _ => {
            assert!(x != 1);
            assert!(x != 2);
            assert!(x != 3);
        }
    }
}

// Signed integer - i32
pub fn single_value_i32(x: i32) {
    match x {
        0 => assert!(x == 0),
        _ => assert!(x != 0),
    }
}

// Signed integer with negative values
// TODO: Commented out - uncovered independent bug where -1 appears as 4294967295
// See https://github.com/creusot-rs/creusot/pull/1899#discussion_r2768099292
// pub fn negative_values_i32(x: i32) {
//     match x {
//         -1 => assert!(x == -1),
//         0 => assert!(x == 0),
//         1 => assert!(x == 1),
//         _ => {
//             assert!(x != -1);
//             assert!(x != 0);
//             assert!(x != 1);
//         }
//     }
// }

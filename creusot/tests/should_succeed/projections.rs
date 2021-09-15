// SHOULD_SUCCEED: parse-print
// Tests that various kinds of projections in Rust successfully translate

pub fn copy_out_of_ref(x: &u32) -> u32 {
    *x
}

fn copy_out_of_sum(x: Result<&mut u32, &mut u32>) -> u32 {
    match x {
        Ok(x) => *x,
        Err(y) => *y,
    }
}

fn write_into_sum(x: &mut Option<u32>) {
    match x {
        Some(y) => *y = 10,
        None => (),
    }
}

fn main() {
    match Some(10) {
        Some(x) => x == 0,
        None => false,
    };
}

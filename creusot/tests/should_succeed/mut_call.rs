extern crate creusot_contracts;

fn kill(_: &mut u32) {}
pub fn test() {
    let mut a = 10;
    kill(&mut a);
}

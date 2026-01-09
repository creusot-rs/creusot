extern crate creusot_std;

pub fn nested_closure() {
    let a = true;
    let _a = (|| {
        let omg = || a;
        (omg)()
    })();
}

extern crate creusot_contracts;

pub fn nested_closure() {
    let a = true;
    let _a = (|| {
        let omg = || a;
        (omg)()
    })();
}

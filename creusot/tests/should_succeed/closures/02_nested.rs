fn nested_closure() {
    let a = true;
    let a = (|| {
        let omg = || a;
        (omg)()
    })();
}

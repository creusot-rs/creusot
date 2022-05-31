extern crate creusot_contracts;

// make sure that local translation handles variable shadowing well
pub fn multiple_scopes() {
    let mut _x = 1;
    let _y = 2;
    {
        let _y = 3;
        _x = _y;
    }
}

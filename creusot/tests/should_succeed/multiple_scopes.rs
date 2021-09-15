// make sure that local translation handles variable shadowing well
fn multiple_scopes() {
    let mut x = 1;
    let y = 2;
    {
        let y = 3;
        x = y;
    }
}

fn main() {}

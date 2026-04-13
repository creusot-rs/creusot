fn main() {
    // This seems to be ignored when emmitted from dependency and I have no idea why.
    println!("cargo:rustc-link-arg=-Wl,-export-dynamic");
}

# Basic concepts

Every Creusot macro will erase themselves when compiled normally: they only exist when using `cargo creusot`.

If you need to have Creusot-only code, you can use the `#[cfg(creusot)]` attribute.

Note that you must explicitly use the `creusot_std` crate in your code (which should be the case once you actually prove things, but not necessarily when you initially set up a project), such as with the line:

```rust
use creusot_std::prelude::*;
```

or you will get a compilation error complaining that the `creusot_std` crate is not loaded.

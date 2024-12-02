# Int in ghost

You can manipulate values of type `Int` in ghost code, by using the `int` suffix on integer literals:

```rust,creusot
ghost! {
    let my_int = 42int;
};
```

Right now you cannot do much except pass it around: operations like `+` or `*` are only supported in pearlite.
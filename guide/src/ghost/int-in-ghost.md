# Int in ghost

You can manipulate values of type `Int` in ghost code, by using the `int` suffix on integer literals:

```rust,creusot
ghost! {
    let x = 42int;
    let y = 58int;
    assert!(x + y == 100int);
};
```

Ghost containers return their length as an `Int`, and `Seq` is indexed by `Int` as well:

```rust,creusot
ghost! {
    let s: Seq<_> = ...;
    let m: FMap<_, _> = ...;
    let len: Int = m.len_ghost();
    let x = s[len + 3int];
};
```

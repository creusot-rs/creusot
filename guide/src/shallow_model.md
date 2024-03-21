# Shallow model

You can implement the `@` operator for your type.
To do that, you just implement the `creusot_contracts::ShallowModel` trait specifying the associated type `ShallowModelTy`.

For example, the following gives a spooky data type `MyPair<T, U>` a nice pair model.

```rust
struct MyPair<T, U>(T, U);

impl<T, U> ShallowModel for MyPair<T, U> {
    type ShallowModelTy = (T, U);

    #[logic]
    #[open]
    fn shallow_model(self) -> Self::ShallowModelTy {
        (self.0, self.1)
    }
}

#[ensures(result@ == (a, b))]
fn my_pair<T, U>(a: T, b: U) -> MyPair<T, U> {
    MyPair(a, b)
}
```

<!-- TODO:
- Shallow model for base types
- explain DeepModel
 -->

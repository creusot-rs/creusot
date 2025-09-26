# Views as models of types

It is generally convenient to map a Rust type to its logical model.
This logical model is the type that specifications and clients then use to describe values of this type in the logic.

In Creusot, this is provide using the `creusot_contracts::View` trait, providing a `view` method mapping the type to a `ViewTy` associated type for the model.

Specifications can then use the `@` operator as a syntactic sugar for `.view()` on a type that implements `View`.

For example, the following gives a spooky data type `MyPair<T, U>` a nice pair model.

```rust
struct MyPair<T, U> {
  fst: T,
  snd: U,
}

impl<T, U> View for MyPair<T, U> {
    type ViewTy = (T, U);

    #[logic(open)]
    fn view(self) -> Self::ViewTy {
        (self.fst, self.snd)
    }
}

#[ensures(result@ == (a, b))]
fn my_pair<T, U>(a: T, b: U) -> MyPair<T, U> {
    MyPair(a, b)
}
```

<!-- TODO:
- View for base types
- explain DeepModel
- talk about sizedness issues and give a workaround (&'static)
 -->

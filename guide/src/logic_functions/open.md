# Visibility of logical functions

By default, `logic` functions are *opaque* outside the module they are defined in (in other words, they are only *open* at the module level).
When a function is opaque, only its pre- and postconditions are visible.
This is useful if the function is only used to express (and prove) that the preconditions imply the postconditions, and we do not care about the result (a *lemma* [^dafny]).
However, if you do want to use the result in a specification outside the module (e.g. if you are using it as a *predicate* in one or more contracts), you use the `open` modifier.
It takes an optional argument, similar to `pub`, e.g. you could specify that a function is to be `#[logic(open(super))]` or `#[logic(open(crate))]`.

```rust,creusot
mod inner {
    // ensures in needed here, as code outside the module will not see the body
    // of this function
    #[ensures(result == x + 1)]
    #[logic]
    pub fn adds_one_closed(x: Int) -> Int { x + 1 }

    // no need for `ensures` here!
    #[logic(open)]
    pub fn adds_one_open(x: Int) -> Int { x + 1 }
}
```

Additionally, you can use the `opaque` modifier to make the logical function fully opaque, even to other functions in the module.
In this case, you cannot attach a specification to the function: you only know that it returns _some_ value (note that this is sound, as all types are inhabited in the logic).
This is one of the only places where you can use the `dead` special keyword, which does nothing but indicate that the function has no implementation.

```rust,creusot
#[logic(opaque)]
fn generate_int() -> Int {
    dead
}
```

[^dafny]: The [Dafny tutorial](https://dafny.org/latest/OnlineTutorial/Lemmas) is a pretty good resource on how to use lemmas.

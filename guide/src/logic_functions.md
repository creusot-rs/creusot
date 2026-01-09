# Logic functions

Functions marked with `#[logic]` can be used in specifications (`requires`/`ensures` and `invariant`) and in `snapshot!`, but cannot be called from normal Rust code.
Typically, `logic` functions manipulate variables of logical model types such as `Int` and `Seq<Int>` rather than normal Rust types such as `i32` and `&[i32]`.

Logical function use normal Rust syntax, but the operators are the logical ones: `==` in a `#[logic]` function does _not_ mean `PartialEq::eq`, but is rather logical equality.
The full [pearlite](./pearlite.md) syntax can be used by opening a `pearlite! { ... }` block.

Logical functions can only call other logical functions, not program functions (and vice-versa).

The `#[logic]` attribute may take additional modifiers in parentheses, like `#[logic(open, prophetic)]`.
Those attributes are described in the following subsections.

## Recursion

When you write *recursive* logical functions, you have to show that the function terminates.

There are two ways to do so:

- If the recursion has a _structural variant_, you have nothing to do. A structural variant is when you `match` on a value, and only use sub-parts of the match in the recursive call:
  ```rust,creusot
  enum List { Nil, Cons(Box<Self>) }

  #[logic]
  fn length(l: List) -> Int {
      match l {
          List::Nil => 0,
          List::Cons(tail) => 1 + length(*tail),
      }
  }
  ```
  In this case, the recursion is accepted by Why3 automatically.
- Else, you need to add a `#[variant(EXPR)]` attribute to the function. Creusot will then check that the expression `EXPR` strictly decreases (in a known well-founded order) at each recursive call.

  The type of `EXPR` should implement the [`WellFounded`](https://creusot-rs.github.io/creusot/doc/creusot_std/logic/trait.WellFounded.html) trait.

## Examples

Basic example:

```rust
#[logic]
fn logic_add(x: Int, y: Int) -> Int {
    x + y
}

#[requires(x < i32::MAX)]
#[ensures(result@ == logic_add(x@, 1))]
pub fn add_one(x: i32) -> i32 {
    x + 1
}
```

Pearlite block:

```rust
#[logic]
fn all_ones(s: Seq<i32>) -> bool {
    pearlite! {
        forall<i: Int> i >= 0 && i < s.len() ==> s[i]@ == 1
    }
}

#[ensures(all_ones(result@))]
#[ensures(result@.len() == n@)]
pub fn make_ones(n: usize) -> Vec<i32> {
    creusot_std::vec![1; n]
}
```

Recursion:

```rust
TODO
```

Prophetic:

```rust
TODO
```


# Mutable borrows

Model of a mutable borrow

## Final reborrows

The above model is incomplete: in order to preserve soundness (see the [Why is this needed ?](#why-is-this-needed-) section), we need to add a third field to the model of mutable borrows, which we call the _id_.

Each new mutable borrow gets a unique id, including reborrows. However, this is too restrictive: with this, the identity function cannot have its obvious spec (`#[ensures(result == input)]`), because a reborrow happens right before returning.

To fix this, we introduce **final reborrows**:

A reborrow is considered final if the prophecy of the original borrow depends only on the reborrow.
In that case, the reborrow id can be inherited:

- If this is a reborrow of the same place (e.g. `let y = &mut *x`), the new id is the same.
- Else (e.g. `let y = &mut x.field`), the new id is deterministically derived from the old.

### Examples

In most simple cases, the reborrow is final:

```rust
let mut i = 0;
let borrow = &mut i;
let reborrow = &mut *borrow;
// Don't use `borrow` afterward
proof_assert!(reborrow == borrow);

#[ensures(result == x)]
fn identity<T>(x: &mut T) -> &mut T {
    x
}
```

It even handles reborrowing of fields:

```rust
let mut pair = (1, 2);
let mut borrow = &mut pair;
let borrow_0 = &mut borrow.0;
proof_assert!(borrow_0 == &mut borrow.0);
```

However, this is not the case if the original borrow is used after the reborrow:

```rust
let mut i = 0;
let borrow = &mut i;
let reborrow = &mut *borrow;
*borrow = 1;
proof_assert!(borrow == reborrow); // unprovable
                                   // Here the prophecy of `borrow` is `1`,
                                   // which is a value completely unrelated to the reborrow.
```

Or if there is an indirection based on a runtime value:

```rust
let mut list = creusot_contracts::vec![1, 2];
let borrow: &mut [i32] = &mut list;
let borrow_0 = &mut borrow[0];
proof_assert!(borrow_0 == &mut borrow[0]); // unprovable
```

### Why is this needed ?

In essence, to prevent the following unsound code:

```rust
pub fn unsound() {
    let mut x: Snapshot<bool> = snapshot! { true };
    let xm: &mut Snapshot<bool> = &mut x;
    let b: &mut Snapshot<bool> = &mut *xm;
    let bg: Snapshot<&mut Snapshot<bool>> = snapshot! { b };
    proof_assert! { ***bg == true && *^*bg == true };
    let evil: &mut Snapshot<bool> = &mut *xm;
    proof_assert! { (evil == *bg) == (*^evil == true) };
    *evil = snapshot! { if evil == *bg { false } else { true } };
    proof_assert! { **evil == !*^evil };
    proof_assert! { **evil == !**evil };
}
```

If borrows are only a pair of current value/prophecy, the above code can be proven, and in particular it proves `**evil == !**evil`, a false assertion.

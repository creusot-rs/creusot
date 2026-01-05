# Linked list

> [!IMPORTANT]
> Get the starting code for this tutorial in the [creusot-rs/tutorial repository](https://github.com/creusot-rs/tutorial).
>
> Open the file [`src/ex2_linked_list.rs`](https://github.com/creusot-rs/tutorial/blob/main/src/ex2_linked_list.rs).

This tutorial demonstrates how we can use Creusot to verify
a data structure manipulating raw pointers.
This data structure uses `unsafe` blocks to dereference raw pointers,
and we can prove that these operations are in fact safe.

A linked list provides an efficient implementation for a queue:
the operations `push_back` and `pop_front` can be performed in constant time.
Moreover, the `push_front` operation is also available in constant time.

To support constant-time `push_back` and `pop_front`, we must be able to
access and modify the linked list from both ends. For that reason,
this data structure is inherently challenging to express in safe Rust.
Hence, we implement this linked list using raw pointers.

A linked list is made of multiple links.
Each `Link` contains a `value` and a raw pointer to the next `Link`.
This pointer may be null, which indicates the end of the list.

```rust
struct Link<T> {
    value: T,
    next: *const Link<T>,
}
```

We keep track of a linked list with two pointers: they point to the first
and last links. If we start from the `first` link and repeatedly follow
`next` pointers, we will eventually reach the `last` link, and
its `next` pointer must be null.

```rust
pub struct List<T> {
    first: *const Link<T>,
    last: *const Link<T>,
}
```

This type implements the following methods:

- `push_back(&mut self, value: T)`: allocate a new `link: Link<T>`, make the `next` field of the current `last` link point to the new `link`, and change `last` to `link`.

- `pop_front(&mut self) -> T`: take out the `first` link, and change `first` to the `next` link.

- `push_front(&mut self, value: T)`.

## Step 1: Ghost permissions

To verify pointer operations, Creusot provides the notion of *ghost permissions*. A *permission* is a token which
keeps track of the data associated with a pointer. This token cannot be duplicated: we leverage Rust's ownership
system to reason about pointer aliasing. Permissions are a ghost resource, which means that they have no run-time impact;
their only use is to enable formal verification.
Pointer permissions play a similar role to points-to assertions in separation logic.

The first step is to make permissions explicit in the data structure.

**Extend the `List` type with a `Ghost` field containing the permissions for the pointers contained in the linked list.**

> [!TIP]
>
> - The type of permissions for pointers `*const T` is [`Perm<*const T>`][perm].
> - [`Perm`][perm] is an unsized type; we can put it in a `Box` when a sized type is expected.
> - As a linked list is essentially a sequence of `Link<T>`, we can store permissions in a sequence ([`Seq`][seq]).
> - To make it compile, we will also need to update `List::new()` to call [`Seq::new()`][seq-new] to conjure an empty ghost sequence.

[perm]: https://creusot-rs.github.io/creusot/doc/creusot_std/ghost/perm/struct.Perm.html
[seq]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html
[seq-new]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.new

<details>
<summary>Solution</summary>

```rust
pub struct List<T> {
    first: *const Link<T>,
    last: *const Link<T>,
    /// Pointer permissions of all list links
    seq: Ghost<Seq<Box<Perm<*const Link<T>>>>>,
}

impl<T> List<T> {
    pub fn new() -> List<T> {
        // Initialize the `seq` field with an empty `Seq`.
        List { first: std::ptr::null(), last: std::ptr::null(), seq: Seq::new() }
    }
}
```

</details>

## Step 2: Type invariant

The permissions in a `List<T>` should correspond to the pointers that it contains.

**Write a *type invariant*, by implementing the [`Invariant`][invariant] trait, to encode this well-formedness condition.**

[invariant]: https://creusot-rs.github.io/creusot/doc/creusot_std/invariant/trait.Invariant.html

It contains one method `invariant(self)`
which defines the property that all values of that type should satisfy.

Creusot will automatically assume type invariants of function parameters as additional preconditions,
and type invariants of results as additional postconditions.
For functions that take mutable borrows as arguments, type invariants are assumed for the initial value
as preconditions, and asserted as postconditions for the final value.

> [!TIP]
>
> - A permission `Perm<*const T>` contains two pieces of data: the [`.ward()`][ward], which is the pointer protected by the permission,
>     and the value ([`.val()`][val]) that the pointer points to.
> - `self.first` must point to the first element: it must be the `ward`
>     of the first element of `self.seq`. Similarly, `self.last` must be
>     the `ward` of the last element of `self.seq`.
> - The links must be chained properly: each link's `next` pointer
>     must be the ward of the next link in `self.seq`, except for the
>     last link, whose `next` must be null. (Hint: use [`is_null_logic`][is-null-logic].)
> - Don't forget the base case!

[ward]: https://creusot-rs.github.io/creusot/doc/creusot_std/ghost/perm/struct.Perm.html#method.ward
[val]: https://creusot-rs.github.io/creusot/doc/creusot_std/ghost/perm/struct.Perm.html#method.val
[is-null-logic]: https://creusot-rs.github.io/creusot/doc/creusot_std/std/ptr/trait.PointerExt.html#method.is_null_logic

<details>
<summary>Solution</summary>

```rust
impl<T> Invariant for List<T> {
    #[logic(inline)]
    fn invariant(self) -> bool {
        pearlite! {
            (*self.seq == Seq::empty() &&
             self.first.is_null_logic() &&
             self.last.is_null_logic())
            ||
            (self.seq.len() > 0 &&
             self.first == *self.seq[0].ward() &&
             self.last  == *self.seq[self.seq.len() - 1].ward() &&
             // the links in `seq` are chained properly
             (forall<i> 0 <= i && i < self.seq.len() - 1 ==>
                 self.seq[i].val().next == *self.seq[i+1].ward()) &&
             self.seq[self.seq.len() - 1].val().next.is_null_logic())
        }
    }
}
```

</details>

## Step 3: View

To formalize the functional correctness of `List` methods, it is convenient
to have a functional model for it, also known as a *view* in Creusot.

**Implement the [`View`][view] trait to define a view.**

[view]: https://creusot-rs.github.io/creusot/doc/creusot_std/model/trait.View.html

A linked list naturally represents a sequence of elements: we define the view
of linked lists as a mapping from `List<T>` to sequences `Seq<T>`.
Thus, a view provides a high-level representation of a data structure,
hiding the details of memory layout.

> [!TIP]
>
> - Use the [`Seq::map`][seq-map] method.
> - The body of `#[logic]` functions should be wrapped in the `pearlite!` macro.

[seq-map]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.map

<details>
<summary>Solution</summary>

```rust
impl<T> View for List<T> {
    type ViewTy = Seq<T>;

    #[logic]
    fn view(self) -> Self::ViewTy {
        pearlite! {
            (*self.seq).map(|ptr_perm: Box<Perm<*const Link<T>>>| ptr_perm.val().value)
        }
    }
}
```

</details>

We are now ready to verify the methods of `List`.

## Step 4: `new`

**Write the contract of `new()`:** the view of the `result` is the empty sequence [`Seq::empty()`][seq-empty].

[seq-empty]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.empty

<details>
<summary>Solution</summary>

```rust
#[ensures(result@ == Seq::empty())]
```

</details>

## Step 5: `push_back`

### Specify `push_back`

**Write the contract of `List::push_back`.**

> [!TIP]
> Use [`Seq::push_back`][seq-push-back].

[seq-push-back]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.push_back

<details>
<summary>Solution</summary>

```rust
#[ensures((^self)@ == (*self)@.push_back(value))]
```

</details>

### Verify `push_back`

We must rewrite the body of the function slightly to make use of the permissions that we've made explicit.
There are three things to do:

1. Replace `Box::into_raw`, which casts the newly allocated `Box` into a pointer,
    with [`Perm::from_box`][perm-from-box], which also returns the associated permission with it.
2. Replace the raw pointer dereference `*(self.last as *mut Link<T>)`
    with [`Perm::as_mut`][perm-as-mut], which requires the pointer's permission.
3. Push the permission (from `Perm::from_box`) into `self.seq`.
    (Hint: `Seq` implements the [`push_back`][seq-push-back] method.)

> [!TIP]
> For steps 2 and 3, use `ghost!` blocks: they enable calling ghost functions
> ([`Seq::len_ghost`][seq-len-ghost], [`Seq::get_mut_ghost`][seq-get-mut-ghost], [`Seq::push_back_ghost`][seq-push-back-ghost], [`Ghost::into_inner`][ghost-into-inner])
> and they are erased at run time.

[perm-from-box]: https://creusot-rs.github.io/creusot/doc/creusot_std/ghost/perm/struct.Perm.html#method.from_box
[perm-as-mut]: https://creusot-rs.github.io/creusot/doc/creusot_std/ghost/perm/struct.Perm.html#method.as_mut
[seq-len-ghost]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.len_ghost
[seq-get-mut-ghost]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.get_mut_ghost
[seq-push-back]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.push_back
[seq-push-back-ghost]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.push_back_ghost
[ghost-into-inner]: https://creusot-rs.github.io/creusot/doc/creusot_std/ghost/struct.Ghost.html#method.into_inner

<details>
<summary>Solution</summary>

```rust
pub fn push_back(&mut self, value: T) {
    let link = Box::new(Link { value, next: std::ptr::null() });
    let (link_ptr, link_own) = Perm::from_box(link);              // 1
    if self.last.is_null() {
        self.first = link_ptr;
        self.last = link_ptr;
    } else {
        let link_last = unsafe {
            Perm::as_mut(
                self.last as *mut Link<T>,
                ghost! {                                          // 2
                    let off = self.seq.len_ghost() - 1int;
                    self.seq.get_mut_ghost(off).unwrap()
                },
            )
        };
        link_last.next = link_ptr;
        self.last = link_ptr;
    }
    ghost! { self.seq.push_back_ghost(link_own.into_inner()) };   // 3
}
```

</details>

## Step 6: `pop_front`

### Specify `pop_front`

**Write the contract of `pop_front`.**

> [!TIP]
> - Use [`Seq::pop_front`][seq-pop-front].
> - We can use `match` in Pearlite.

[seq-pop-front]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.pop_front

<details>
<summary>Solution</summary>

```rust
#[ensures(match result {
    None => (*self)@ == Seq::empty() && (^self)@ == Seq::empty(),
    Some(x) => (*self)@.len() > 0 && x == (*self)@[0] && (^self)@ == (*self)@.pop_front()
})]
```

</details>

### Verify `pop_front`.

As before, we must modify the function to manipulate pointer permissions.

1. Pop the first permission from `self.seq`. (Hint: use [`Seq::pop_front_ghost`][seq-pop-front-ghost].)
2. Replace `Box::from_raw`, which casts a pointer to a `Box`, with [`Perm::to_box`][perm-to-box],
    which also requires the permission protecting the pointer.

[seq-pop-front-ghost]: https://creusot-rs.github.io/creusot/doc/creusot_std/logic/seq/struct.Seq.html#method.pop_front_ghost
[perm-to-box]: https://creusot-rs.github.io/creusot/doc/creusot_std/ghost/perm/struct.Perm.html#method.to_box

<details>
<summary>Solution</summary>

```rust
pub fn pop_front(&mut self) -> Option<T> {
    if self.first.is_null() {
        return None;
    }
    let own = ghost! { self.seq.pop_front_ghost().unwrap() };              // 1
    let link = unsafe { *Perm::to_box(self.first as *mut Link<T>, own) };  // 2
    self.first = link.next;
    if self.first.is_null() {
        self.last = std::ptr::null_mut();
    }
    Some(link.value)
}
```

</details>

## Step 7: `push_front`

Follow the same recipe as `push_back` and `pop_front`.

## Conclusion

We now have a verified implementation of linked lists.
This data structure makes use of unsafe primitives, and Creusot formally
verifies that their safety conditions are satisfied.

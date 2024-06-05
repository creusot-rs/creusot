# Base types

Most type have a very simple interpretation in Why3:

- The interpretation for a scalar type (`i32`, `bool`, `f64`, ...) is itself.
- The interpretation of `[T]` is `Seq<T>`, the type of sequences.
- The interpretation of `&T` is the interpretation of `T`.

  Creusot is able to assume that `T` and `&T` behave the same, because of the "shared xor mutable" rule of Rust: we won't be able to change the value (interior mutability is handled by defining a special model for e.g. `Cell<T>`), so we may as well be manipulating an exact copy of the value. 
- The interpretation of `Box<T>` is the interpretation of `T`.

  This is because a `Box` uniquely own its content: it really acts exactly the same as `T`.
- Structures and enums are interpreted by products and sum types.
- The interpretation of `&mut T` is a bit more complicated: see the next section.

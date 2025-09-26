Creusot is a deductive verifier for (safe) Rust code built on top of the [Why3](https://why3.lri.fr) verification platform.
This document describes the overarching approach and the structure of the translation that Creusot performs.

With Creusot you can write normal Rust code, annotate it with contracts and run it through Creusot to prove that your code will always satisfy your contracts.

```rust
#[requires(false)]
#[ensures(true)]
fn my_cool_code(param1 : T) -> bool {
	...
}
```

These kinds of tools have been developed for many languages, with varying degrees of success.
In particular the presence of *mutable pointers* usually causes issues, they are hard to model and force tools to do complex reasoning, which in turns makes them much less usable.
A key idea behind Creusot is that we can use Rust's type system to simplify verification when using mutable borrows.

# The Trick

One of the keys to Creusot's translation is its representation of *mutable borrows*, based on the work of RustHorn.
In this model, each borrow is represented by a pair of a current and a final value, which is *prophecised*.
When the borrow ends, we *resolve* the prophecy, linking it to the value stored in the borrow at the moment of ending.
For a more complete explanation of how this aspect works, you can read the following papers:
- RustHorn ([10.1145/3462205](https://dl.acm.org/doi/full/10.1145/3462205))
- RustHornBelt ([10.1145/3519939.3523704](https://dl.acm.org/doi/abs/10.1145/3519939.3523704))
- TODO: JFLA

The key takeaway is that:

> **Mutable borrows can be represented efficiently without separation logic**

Creusot is built on this insight, we translate Rust programs to **pure, functional** programs.
By targeting pure functional programs we can leverage extremely powerful automation for proving functional programs that already exists.
The thesis of Creusot is that this allows for a an asymptotic improvement to the difficulty of verifying pointer programs.

# Input Language

To Creusot programs consist of 3 different kinds of functions:

- **Program functions**: These are normal Rust functions, they may be annotated using the `ensures`, `requires` and `variant` macros. Internally they may also make use of `invariant` to annotate loop invariants.
- **Logical functions**: These functions **do not exist at runtime**, they exist purely during proofs.
They may be used inside specification clauses and are written in a language called *Pearlite*, a specification language for Rust which gives them additional expressive power.
We will cover Pearlite in a future section
- **Hybrid functions**: Hybrid functions are functions which are both logical and program functions.
They must therefore be side-effect free, and can be used equivalently in specifications or programs. Here, think of `Vec::len` as an example.

## Pearlite

Pearlite is the Rust specification language used by Creusot.
It is meant to feel as natural as possible to a Rust user while adding the features needed by a specification language.
Thus, at its core Pearlite expressions consist of the *pure* subset of Rust expressions.
In particular, you have bindings, function calls, arithmetic, etcc.. but you cannot borrow or create **mutable** bindings!
To this fragment of Rust we add a few special operators and syntax:
- **Quantifiers**: We have `forall` and `exists` to perform quantification of propositions
- **Logical Equality**: A special built-in function `equals` performs *logical equality*, even for types which aren't `Eq`
- **Current (`*`) and Final (`^`)**: These two unary operators can only be applied to values of type `&mut T`, and return the current value of the borrow (aka dereference), or its final, *prophetic* value.

### Type System

Pearlite has the same typesystem as Rust, but **does not have ownership**.
It makes no sense to restrict the usage of values in a logical environment, they aren't machine resources anymore.


# Architecture

The following sections will discuss the architecture of Creusot as a system, what the major pieces are and how they fit together.

The project is composed of a few main crates which we will cover in the following sections:
- `creusot`: Implements the compiler, and provides the binaries to run things. Could probably be split up into a few crates at some point.
- `creusot-contracts`: The crate that provides the specification macros for users. Also provides primitives for various logical operations (equality, resolution, quantification, mathematical integers).
- `creusot-contracts-proc`: Proc macro crate for `creusot-contracts`
- `why3`: A why3 AST / printer.

## Binaries

The binaries are structured following the pattern laid out by [flowistry](https://github.com/willcrichton/flowistry):

- `cargo-creusot`, a cargo extension which provides a cargo-like compilation of a project with creusot
- `creusot-rustc`, a rustc wrapper which provides rustc-like interaction with creusot.
- `creusot-driver`, an internal binary which does the actual work.

## Main Loop


## Program functions

Each function is translated as a standalone Why module containing a single coma function.
We translate program functions from the *MIR* of a program, as we need to ensure that borrow checking succeeds and also use dataflow analysis on the MIR body.

### Encoding contracts

When a function is annotated with a contract (`ensures`, `requires`), the relevant proc-macro rewrites the function to leave an annotation which we can use to recover the contract during compilation.

```rust
#[ensures(prop)]
fn x(param1, param2, ...) -> T { .. }
```

Is transformed into

```rust
#[creusot::item="x_ensures_$UUID"]
fn x_ensures_$UUID(param1, param2, ..., result: T) -> bool {
	PROP
}

#[creusot::spec::ensures="x_ensures_$UUID"]
fn x(param1, param2, ...) -> T { .. }

```
We lift specification clauses to top level functions which have the same parameters as the original function.
The `ensures` macro also gets access to an additional `result` parameter which has the type of the return type of the original function.

We label the lifted specification with `creusot::item` to be able to easily find it later.
It suffices to look at the attributes of the function we're compiling to then be able to easily recover its specifications.
The `prop` which is originally written in Pearlite, is encoded as a HOAS term in Rust.
The section on compiling specifications will cover how this works

### Translating functions

The translation of program functions occurs statement-by-statement from the MIR to coma.
Most MIR statements have an obvious translation, but there are a few key technicalities.

#### Translating Places

Translating a place requires special attention.
In MIR we will often have places like `* _1.0.1 as Some`, to make matters worse, these places can appear in both the left and right hand sides of a statement (ie: assignment).

First, lets consider the simple case where the `Place` appears on the right hand side of an `=`.
Unfortunately, WhyML does not have positional accessors like `.N` nor can we simply downcase to a specific constructor.
However, we can still give a pretty alright translation by using irrefutable let-bindings.

- `P as Cons` becomes `P`, we ignore downcasting, as they are actually handled when we positionally access a field of the downcasted constructor.
- `P.0` becomes `let Cons(a, ..) = P in ...`, note, we introduce a binding here
- `* P` becomes `P.cur` if it is a mutable borrow and `P` otherwise
- Other cases unhandled.

Translating the lefthand side of an assignment is slightly more complex.
The key idea is to forward all the irrelevant parts of the value being updated to produce a new copy with just the target place updated.

- `(P as Cons).0 = V` becomes `let Cons(_, b, c, ...) = P in Cons(V, b, c, ..)`
- `* P = V` becomes `{ current = V, final = P.final}`

These operations are both applied recursively, building up larger accessors and writers from these patterns.

#### Translating `discriminant` / `switchInt`

By the time that we lower to MIR, matching on constructors in Rust has been replaced by matching on the *discriminant* of the type and then switching using `switchInt` in MIR.
However, Why3 cannot actually perform matches on literal values, so this is a slight issue.
Instead, we replace the `discriminant` / `switchInt` pair with a match directly on the values construct in Why3.

## Logical functions

Logical functions are created by `#[logic]` or `#[predicate]`.

## Specifications

All forms of specifications, both logic functions and contract clauses are encoded in the same manner.

### Parsing Pearlite

During macro execution we parse the relevant logical expression using a custom fork of `syn`.
This allows us to extend the syntax of Rust with custom operations.
Once we've actually parsed the expression we print it back in a HOAS-like style, encoding all the custom syntax as stub functions. For example the expression:

```rust
exists<i : Int> i == 0
```

becomes

```rust
creusot_contracts :: stubs :: exists (| i : Int | { i == 0 })

```

Each stub is given the appropriate type so that type checking can then succeed.

### Typechecking Pearlite

When Creusot then starts compiling a logic expression it starts by running it through the Rust type checker.
Once that happens we recover the THIR for translation.
Since Pearlite has no notion of ownership, we prevent the borrow checker from running on any specification expressions.

### Translating Pearlite to WhyML

From THIR we emit WhyML functions.
Each stub symbol is replaced with the correct logical operation, while the rest of the expressions are translated recursively in the obvious manner.

# Translation

## Represention of Rust Items

Each Rust item is translated to a WhyML module.
Generic types become opaque types declared within this module.
Predicates are then a question of 'cloning' the relevant module with the correct substitution.

## Translation of traits

Each trait is translated as a module which includes the signatures of all member methods.
**Note**: This will soon change, traits will instead be translated into a *set* of modules, one for each method.

## Translation of trait implementations

Each trait implementation becomes a module which clones the trait module, instantiating it with the modules of each relevant method.

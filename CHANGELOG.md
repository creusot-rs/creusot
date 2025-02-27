# Changelog

Following is the changelog of Creusot, a verification tool for safe Rust programs. Using Creusot you can prove -- formally -- that your Rust program behaves in a specific manner.

Creusot allows you to annotate your code using *contracts* which describe correctness conditions for your program. Creusot then uses SMT solvers to check that these contracts hold for all possible runs of the program. All of this is done statically without running your program, and contracts are erased at compilation time.

Creusot is currently best suited for the verification of code like data-structures or algorithm implementations, and less so for systems which interact heavily with the outside world or exploit concurrency. Notable projects using Creusot include the [CreuSAT](https://github.com/sarsko/creusat) verified SAT solver and the [Sprout](https://github.com/xldenis/cdsat) SMT solver.

**Creusot is still very experimental software, you should expect some obscure crashes and missing features.**

<!-- next-header -->

## [Unreleased] - ReleaseDate

### Main features

#### Bitwise mode

The new `#[bitwise_proof]` attribute makes Creusot interpret machine integers as bit vectors instead of bounded integers,
giving meaning to bitwise operations.
Bitwise operators have an abstract specification when this attribute is not on.

Along with this feature, Pearlite is also extended with:

- arithmetic operations on machine integers, with a wrapping semantics;
- casts (`n as usize`).

Thanks to Laurent Schneider @laurentder.

#### Closure inference

Contracts for closures can now be omitted, to be inferred through Coma's novel `extspec` mechanism.

#### Prove with Why3find

The new command `cargo creusot prove` launches Why3find to automatically
generate proofs. This removes the need for manually editing sessions through
the Why3 IDE. The Why3 IDE remains useful to debug incomplete proofs,
via `cargo creusot prove -i`.

This more automated solution prevents the use of manual transformations,
such as `exists` to instantiate existential quantifiers.
This may require restructuring code to be more proof-friendly.
There are known challenges of that sort surrounding the specification
of iterators in `creusot-contracts`.

#### Documentation

- The [Creusot tutorial](https://creusot-rs.github.io/creusot/guide/tutorial.html) is an introduction to verify Rust programs with Creusot.
- The `creusot-contracts` API documentation is [available online](https://creusot-rs.github.io/creusot/doc/creusot_contracts/). It contains information about Creusot's attributes and macros (supplementing the [guide](https://creusot-rs.github.io/creusot/guide/)), and lists available functions and methods along with their contracts, including logic functions (which would be omitted by a simple `cargo doc`).

### Other improvements

#### Installation

The new `./INSTALL` script handles installing Creusot and tools (Why3, Why3find, and SMT solvers). It assumes that `cargo` and `opam` are installed.
In particular, `./INSTALL` creates an Opam switch dedicated to Creusot to ensure Why3 and Why3find remain available at their expected versions.

Just run `./INSTALL`.

#### Setting up new projects

The `cargo creusot new` and `cargo creusot init` generate the boilerplate to
get you started with a new verified Rust project.

#### Build with stable Rust compiler

Rust code containing Creusot contracts can now be compiled with a stable Rust compiler.
This is made possible by the following changes:

- make `creusot-contracts` buildable with a stable Rust compiler;
- hide `#[invariant(...)]` attributes, whose parsing requires the unstable features `proc_macro_hygiene` and `stmt_expr_attributes`.

#### Coma

Type translations are inlined in modules that use them. With this change, every Rust function is translated to a standalone module.

Improved metadata on goals: source spans are more accurate and labels are more informative (ensures, requires, and invariants are numbered).

The `prelude` (the Coma library imported by Creusot-translated artifacts) has been renamed to `creusot`.

### Standard library (`creusot-contracts`)

- Add extern specs for `get_unchecked` and `get_unchecked_mut` (slice methods) (#1382).
- Add `Mapping::index_logic` (you can write `f[x]`) and `such_that` (#1296).
- Implement `Clone` on `Seq`, `FMap`, `FSet` (#1289).
- Add `FMap::index_logic` (#1254).
- Rename `Seq::{push,pop}` to `{push_back,pop_back}`, add `{push_front,pop_front}` (#1224).
- Add `std::cmp` and `Ord` functions (#1305).
- Add specs for `HashSet`, `FSet`, and some iterators (ranges, `filter_map`, `rev`) (#1313).
- Implement `View`, `DeepModel`, and `Default` for `char` (#1381).

#### Iterators

- Add `Iterator` impls for `[T;N]` and `&mut I` (#1290).
- Add specs for iterators of `HashMap` and `HashSet` (#1306).
- Remove redundant `inv` in iterator specs (#1291).

#### Ghosts

- Add `PCell`: interior mutability with ghost ownership (#1262).
- Enable logic data structures to be used in ghost code (#1073).
- Add `Int` literals for ghost code, e.g, `1int` (#1256).
- Allow arithmetic operators on `Int` in ghost code (#1281).
- Add specs for raw pointers and ghost ownership for pointers (#1169).
- Add `FMap::split_mut_ghost` (#1356).
- Fix spec of `FMap::get_mut_ghost` (#1253).
- Strengthen `PtrOwn::disjoint_lemma` (#1295).

## [0.3.0] - 2024-10-27 

### Cargo Creusot

Documentation using `cargo creusot doc`  now includes functions specifications and logic function bodies (Arnaud Golfouse @arnaudgolfouse).

Proof obligations are now generated in a separate `verif` directory, and by default `cargo creusot` will generate one coma file per module in your program, this can enable faster iteration by only loading relevant submodules during verification.
The old behavior can be restored by passing the `--monolithic` flag.

Note: We are planning on removing the `--focus-on` option with the arrival of modular code generation.

The `cargo creusot why3 ide` has been made aware of this behavior.

### Creusot IDE

Not strictly speaking part of this release, we have recently published a new [Creusot IDE](https://github.com/creusot-rs/creusot-ide) extension on the VSCode Marketplace.
The extension currently provides syntax highlighting for Creusot, and dynamically updates the proof status within VSCode.

It also has support for running `why3find` on proofs that have pending obligations by interacting with an icon in the sidebar.


### Pearlite

Several minor but still important changes were made to Pearlite in this release, their descriptions follow.

#### Nested Trusted

The semantics of `#[trusted]` were slightly altered, the attribute is now inherited, which means that placing it on a module marks all contained functions as trusted. (Xavier Denis @xldenis, request by Molly MacLaren @mojeanmac)

#### Type invariants & Resolution

Type invariants were completely overhauled, several unsoundnesses were resolved in the process.
Invariants are now added as pre and post conditions to program functions, but are not enforced for logical constructs.

Logical functions and quantifiers no longer provide the invariant, meaning that you must explicitly guard them if you require the invariant to be upheld for a type.  This enables future support for empty types.

The resolution trait no longer uses specialization (meaning you no longer have to add `min_specialization` to your projects). Users should also now use the new, bare `resolve` functions if needed.
Resolution also comes with a proof obligation to demonstrate the soundness of user-provided implementations of the `Resolve` trait.

#### Syntax changes & bug fixes

New syntax to specify triggers in quantifiers (David Ewert @dewert99). Triggers can be added to quantifiers in the following way: `forall<x : T, .. > #![trigger exp1,..,expN] exp`.
Multi-triggers are supported by providing multiple comma separated values.

Fixes to `#[derive(DeepModel)]` for structs (Arnaud Golfouse @arnaudgolfouse).


#### Creusot standard library

The API support for `VecDeque` was extended, adding indexing, and a custom `Resolve` implementation. (David Ewert @dewert99)

New specifications for `map` and `filter` were added. While proven, the specification for `filter` is currently hard to successfully apply in projects, we expect revisions in future releases.

Several changes were made to the `GhostPtrMap` module. (@dewert99)

The `ShallowModel` trait was renamed to `View` which is hoped to be less confusing. (Armaël Guéneau @armael)

### Creusot Backend

#### Place-oriented reasoning

This release marks the complete transition of Creusot to a fully "place oriented" mode of reasoning.
For users, what this means, is generally an easier time working with type invariants, specifically with partially initialized structures and the closing of several lingering unsoundnesses.

#### Closures

Several crashes with regards to closures (especially nested) were fixed.
Support was added for `proof_assert!` inside of closures.

#### Structural Resolution

A new intrinsic `structural_resolve` generates a resolution statement from the conjunction of fields of a type. All user-defined implementations must be *weaker* than this.

#### Ownership in Ghost code

An initial, experimental version of ownership in ghost code was added, reintroducing the `ghost!` macro. Future releases will flesh out support in this area. (@arnaudgolfhouse)

#### Coma

A major unsoundness in our encoding of pattern matching in Coma was solved. We found that this was exploited by solvers in a single test of our suite (though without affecting the end reuslt of the proof).
The issue was resolved.

Identifiers generated in Coma are now stable, meaning that re-organizing Rust code should not lead to any changes in generated proofs. This should improve the obsolecence of proofs in Why3. (Li-yao Xia @Lysxia)

### SMT Solvers

The Alt-Ergo solver was upgraded to version 2.6.0. As a bonus, it is now installed by `cargo creusot setup` itself instead of `opam`. (Armaël Guéneau @armael) 

## [0.2.0] - 30/07/2024

### Cargo Creusot

Cargo creusot saw several minor improvements especially with regards to configurations.

Users upgrading from `v0.1` will need to regenerate their configuration by running `cargo creusot setup install`.

### Pearlite

This release introduces the foundations of termination checking in Creusot by providing two new macros: `#[terminates]` and `#[pure]`.

- `#[terminates]` indicates that a function terminates, these functions are allowed to crash or run out of memory.
- `#[pure]` these functions are *total*, they must terminate and cannot exhibit *any* side-effects.

The termination check generated by Creusot is currently overly conservative and does not support loops or mutally recursive functions.
We expect to lift this restriction in future releases.

While `terminates` functions may call either `pure` or `terminates` functions, `pure` can only call other `pure` functions.

### Creusot Backend

This change should mostly not be user-visible, but we want to disclose it both to encourage users to bring up any problems they encounter when moving to 0.2 and to share our vision for future releases.

Version 0.2 marks the transition of Creusot to the new intermediate verification language [Coma](https://coma-ivl.codeberg.page/quickstart.html). Coma is designed as a modern kernal language for the Why3 platform and offers incredible flexibility while keeping an extermely minimal core. This replaces our usage of MLCFG in Creusot as the language we target.

Using Coma we have a solution for the specification of closures which could allow us to elide significant portions of specifications in proofs.
We don't currently leverage this, but expect it to be ready by version 0.3.

We expect the primary noticable change to be a regression in the labels for proof tasks in logical functions, if you notice any other regressions including newly failing proofs, please report them on github.


### Why3find support

The code generated by Creusot was changed to be drop-in compatible with [`why3find`](https://git.frama-c.com/pub/why3find), an alternative cli-driven frontend for why3.
You can run `why3find prove creusot_generated_file.coma`, so long as the directory this is run in contains a copy of the `prelude` folder of Creusot.
Future verisons will integrate this natively into `cargo creusot`.

## [0.1.1]

This release contains a major bug fix for `cargo creusot` fixing the loading of metadata for crates such as `creusot-contracts`. If your proofs were not passing before, this may be why. 

It also bumps the associated version of why3 to 1.7.2 from 1.7.1




The following are the release notes for the first official version of Creusot, a verification tool for safe Rust programs. Using Creusot you can prove -- formally -- that your Rust program behaves in a specific manner. 

Creusot allows you to annotate your code using *contracts* which describe correctness conditions for your program. Creusot then uses SMT solvers to check that these contracts hold for all possible runs of the program. All of this is done statically without running your program, and contracts are erased at compilation time.

Creusot is currently best suited for the verification of code like data-structures or algorithm implementations, and less so for systems which interact heavily with the outside world or exploit concurrency. Notable projects using Creusot include the [CreuSAT](https://github.com/sarsko/creusat) verified SAT solver and the [Sprout](https://github.com/xldenis/cdsat) SMT solver. 

Since this is the first release of Creusot, we will cover the currently implemented features and aspects of Rust which are supported. 

*Creusot is still very experimental software, you should expect some obscure crashes and missing features.* 

## Getting Started with Creusot

To get started as a user with Creusot, we recommend checking out the [README](https://github.com/creusot-rs/creusot/blob/master/README.md).

## Cargo Integration

Creusot provides the `cargo creusot` binary which serves to make verification of crates simple. 
To get started with Creusot, you can run `cargo creusot` on your crate, generating proof obligations in `target/your-crate.mlcfg`. 
These proof obligations can be discharged using Why3 and the Why3 IDE. 

### `cargo creusot setup`

To help you manage your Creusot and Why3 installations, we provide `cargo creusot setup`. 
Through this command you can install, or view the Creusot specific Why3 configuration and prover installations. 

```
Setup and manage Creusot's installation

Usage: creusot setup <COMMAND>

Commands:
  status   Show the current status of the Creusot installation
  install  Setup Creusot or update an existing installation
  help     Print this message or the help of the given subcommand(s)

Options:
  -h, --help  Print help
```

`cargo creusot setup install` can currently download and install binaries for `CVC4`, `CVC5` and `Z3`. Eventually it will also be capable of installing `Alt-Ergo` and `Why3` for you (currently these need to be installed separately using opam). See the README for detailed installation instructions.

'External' versions of supported provers can be provided via the `--external` flag.  

## Supported Language Features

Creusot supports a large portion of the Rust language, some of these language constructs are listed below:

### Basic Language constructs

**Control flow:** All control flow syntax is supported:`while`, `loop`, `for`, `if`, `else`, `let if`, `let else`, `break`, `continue`, etc.. 

**Borrows** Creusot has complete support for all forms of borrowing in Rust. **This includes mutable borrows**. You can create borrows, reborrow fields, store borrows in types, **all operations on borrows are supported**. 

### Traits

**Traits Decls & Impls:** Curently, we support traits with associated methods types, and constants. We also handle implementations of these traits.
GATs are currently unsupported.

**Bounds:** We support trait bounds involving associated types. 
Bounds involving GATs, const generics, or HRTB are unsupported. 

**Trait Objects**: Trait objects are not supported.

### Closures

Creusot supports most closures in Rust, including `FnOnce`, `FnMut` or `Fn`, and we also support `move` closures. Async closures are not supported as Creusot does not support `async` code currently. 

### Iterators

By building off our support for closures and traits, we provide extensive support for iterators and iterator chains in Creusot. 

## Unsupported Language Features

Equally important are the parts of Rust which are unsupported by Creusot, if your code uses these you will need to rewrite it before Creusot can help you verify your code.

### Async

Async code is currently unsupported by Creusot, we do not support generators or coroutines in our encoding. 

### Unsafe

Creusot's verification relies on the Rust type system's ownership so we cannot verify code using raw pointers. 
When raw pointers are encountered, Creusot will not crash but instead generate verification conditions which will be unprovable for almost anything. 
This allows trivial usage of mutable pointers for things like `vec![]`.

### Trait Objects

We do not currently support trait object reasoning. Like with raw pointers we generate verification conditions which are useless for anything beyond the most trivial checks.
This allows usage of `println!()` or similar macros to work. 

### HRTB & GATs

Advanced features like Higher-Ranked Trait Bounds or Generic Associated Types are not currently supported by Creusot.

## Specification Language: Pearlite

To enable verification, Creusot provides a *specification language* called Pearlite which you can use to annotate your code with assertions code must satisfy. Pearlite includes many features that are targeted to make specific kinds of Rust code verifiable, which we will list below.

### Contracts & Assertions

Pearlite provides several forms of contracts you can use to specify your code:

- `#[requires(..)]` specifies a precondition for a function. This accepts a Pearlite expression as argument. Requires clauses will be checked at all program function call sites.
- `#[ensures(..)` specifies a postcondition for a function. Accepts a Pearlite expression. Creusot will check that all function exits uphold the postcondition. 
- `#[variant(..)]` specifies a *variant* which can be used to show that a function terminates. A variant clause must evaluate to a type with a strictly decreasing, finite size (aka a well-founded order in math speak). Examples of this are positive integers, or any Rust type defined with `Box`. This will be enforced at all recursive calls. 
- `#[invariant(..)]` specifies a *loop invariant*, a property which is true throughout every iteration of a loop. Invariants are the only thing Creusot uses to reason about the behavior of loops. This is checked at loop entry and at the end of each loop iteration.
- `proof_assert!(..)` is a Pearlite analogue to Rust's `assert!` macro. It allows you to assert the truth value of a Pearlite expression, which may mention ghost code. 
- `#[trusted]` tells Creusot not to generate any proof obligations for the attached function. 
### Pearlite Expressions

Pearlite is a *total*, *functional* language with a syntax similar to Rust. It extends the syntax of Rust expressions in several minor ways, and more importantly has different *semantics*, implied by its totality.
This means that operations like `a + b` are always defined, even for values which would panic in ordinary Rust. Instead, in Pearlite they would produce an *unspecified value*.

#### Basic Syntax

Pearlite syntax corresponds of basic Rust expressions: variables, literals, let bindings, if-else, match, function calls & type constructors, extended with a few new operations.
We provide quantifiers `forall<x : T, ..> expr` and `exists<x : T, .. > expr` for univeral and existential quantification respectively. 
We also have the postfix "model" operator `@` which is a sugar for Creusot's `ShallowModel` trait. 
The most important operation in Pearlite is the `^` final operator which is used to dereference a mutable borrow at the end of its lifetime. 

Pearlite can be written in two different ways, either as ordinary Rust, in which case you are restricted to the Rust syntax fragment of Pearlite, or using the `pearlite!{}` macro which provides our additional syntax:

```
#[predicate]
fn my_function(x: Int) -> bool { 
    x >= 0 // can use basic pearlite here
}

#[predicate]
fn exists_inverse(y : Int) -> bool {
 pearlite! { exists< x : Int> x + y == 0 }
}
```

Pearlite contract clauses are implicitly wrapped in a `pearlite!` macro invocation.
 
#### Mutable Borrows

Rust code uses lots of mutable borrows, so having an efficient method for reasoning about them and proving code using borrows is important.
Pearlite provides the `^` final value operator which mirrors `*` by dereferencing in the "future" of a borrow. 

Using this we could specify a simple increment function as follows:

```rust
#[requires(x < 1000u32)]
#[ensures(^ x == *x + 1u32)]
fn incr(x : &mut u32) { *x += 1}
```
This postcondition can be read as "the final value of x is its initial value + 1".

Where the `^` final value becomes particularly handy is when functions return mutable borrows, like the following:

```rust
#[ensures(^ result == (^x).0)]
#[ensures(* result == (* x).0)]
fn project(x: &mut (u32, bool)) -> &mut u32 {
    &mut x.0
}
```

By adding this postcondition stating that the final value of the result is the same as the final value of the first field of `x`, Creusot can track updates to the `x` through the returned borrow. 

This kind of code which mirrors a specification for the current and final values is so common that we also provide "logical (re) borrowing" as a syntactic sugar. The prior example could instead be written as:

```rust
#[ensures(result == &mut x.0)]
fn project(x: &mut (u32, bool)) -> &mut u32 {
    &mut x.0
}
```

### Logical Types

In verification, we often want to use abstractions which have nicer mathematical properties than real-world types and values (like unbounded integers, mathematical sets, etc...). 
Several of these types are provided as part of the Pearlite standard library:
- `Int` the type of mathematical integers. You can convert a machine integer to an `Int` by taking its model `x@`.
- `Seq<T>` the type of sequences, useful for reasoning about arrays and vectors
- `FSet<T>` the type of *finite* sets.
- `Map<A, B>` the type of mappings from `A` to `B` (aka, functions between `A` and `B`). 

### Predicates and Logical functions

Users can define their own Pearlite functions and predicates through the `#[logic]` and `#[predicate]` attributes. 
When these attributes are attached to a function, they will be interpreted as Pearlite definitions and available in contracts but not in programs. 

Logical functions and predicates can be given contracts, and will then generate proof obligations to make sure those contracts hold. 
However, it is well defined to call a logical function even with values that do not satisfy its precondition: the output will then be an (unspeficied) value which does not uphold the postcondition.

Several modifiers can be applied to Pearlite functions:

- `#[open(path)]` specifies the *opacity* of a definition, an important concept which controls which proofs can see the body of a definition and which see only a symbol.
- `prophetic`, `#[predicate]` and `#[logic]` can accept a `prophetic` argument `#[predicate(prophetic)]` which enables access to the final operator `^`. 

### Ghost code 

Pearlite currently supports a basic form of ghost code known as *snapshots*. Using the `snapshot!` macro you can take a "copy" of a Rust value at a given point in time to use in your proofs. This can be useful to reason about the evolution of state in loops like the following sort routine:

```rust 
  let old_v = snapshot! { v };
    let mut i = 0;
    #[invariant(sorted_range(v@, 0, i@))]
    #[invariant(v@.permutation_of(old_v@))]
    while i < v.len() {
        if i == 0 || v[i - 1] <= v[i] {
            i += 1;
        } else {
            v.swap(i - 1, i);
            i -= 1;
        }
    }
```

We use the snapshot before the loop to ensure that we are only permutting elements which were originally in our array, not adding or removing them. 

### Trait laws & Refinements

Trait declarations can include logical functions and predicates, along with contracts on their program functions.
Each implementation of the trait will then have to prove that they are at least as precise as the contract, their preconditions must be no more strict and their postcondition cannot be weaker than the trait signature itself. 

Often, there are certain properties which are useful for reasoning about types which implement a given trait, like how `Ord` describes a *total order* and should be transitive, anti-symmetric and reflexive. 
These kinds of properties are called "laws" and can be enforced by adding a trait item marked with the `#[law]` attribute and appropriate contract. 
Creusot will automatically consider all possible laws when generating proof obligations, alleviating the user from having to remind the tool about these properties. 

### Closure Contracts

When working with closures, contracts gain a few additional powers.
First, contracts of closures can mention the captured variables. These will have the same type as the Rust variable, that is, if a closure captures `x: T` by mutable borrow, the contract will still see `x` as having type `T` not `&mut T`. 
Additionally, in postconditions we can use the `old(..)` function to refer to the value of a capture *before* the call. `old(..)` can only be applied to captured variables of a closure. 

Note, the contracts of a closure are not allowed to capture additional variables. 

### Type Invariants

Certain types have additional "validity" properties beyond what is allowed by their constructors. 
These properties can be enforced by implementing the `Invariant` trait provided by Creusot. 
This trait declares a type as having a "type invariant" which must be enforced defined points: when a value is being passed to a function, when a value is being returned, and when a value a borrowed value ends its lifetime. 
Creusot will automatically instrument your code with the relevant invariant checks for types which implement this trait. 

### Extern Specs

Because verified Rust code must inevitably interact with the unverified outside world, we provide the `extern_spec!` macro which allows you to assume that outside functions satisfy a contract. 

The macro accepts a set of Rust modules describing the path of the functions being specified:

```rust
extern_spec! {
    mod std {
        mod mem {
            #[ensures(^dest == src)]
            #[ensures(result == *dest)]
            fn replace<T>(dest: &mut T, src: T) -> T;
        }
    }
}
```

Calls to externally specified functions will have their contracts enforced. 

Extern specs are also allowed to refine trait bounds: this is useful for when you need a generic function to only accept "well behaved" types, like in the following: 

```rust=
extern_spec! {
    mod std {
        mod cmp {
            trait PartialEq<Rhs> {
                #[ensures(result == (self.deep_model() == rhs.deep_model()))]
                fn eq(&self, rhs: &Rhs) -> bool
                where
                    Self: DeepModel,
                    Rhs: DeepModel<DeepModelTy = Self::DeepModelTy>;
            }
        }
    }
}
```

We require that the types of `eq`'s parameter implement the Creusot specific `DeepModel` trait, allowing us to use `deep_model` in its specification.

When an extern spec has refined trait bounds, Creusot will enforce that all trait implementations and function calls respect these bounds.

### `creusot-contracts`

Pearlite is provided as part of the `creusot-contracts` crate which ships with a set of `extern_specs!` for parts of the Rust standard library and various useful logical functions, types and traits. 

Some of the specified types & traits are:
- `Vec`
- `Deque`
- `[T]`
- `std::mem`
- `Box`
- `Range`
- `Clone`, `Copy`, `PartialEq`, `PartialOrd`
- `FromIterator` and `IntoIterator`
- `Iterator`:  We provide support for the following adapters
    - `skip`
    - `take`
    - `repeat`, `cycle`, `empty`, `once`, `collect`
    - `enumerate`
    - `cloned`, `copied`
    - `fuse`
    - `zip`
    - `map` (via `map_inv`)
    - Implementations of iterator for core types like `Vec`, `[T]`, `[T; N]`, `0..n` are supported. 

We also provide logical types like `Int`, `Map`, `FSet`, `Set`, `Seq`, along with useful apis for each of those types. 

## Conclusion

Thanks for your interest in Creusot, we hope it will be of use to you! 

There are many small contributions and features which have gone unlisted, but we hope to have described the essential ones. 
Going forward, we'd like to make more frequent releases, avoiding the issue of having a giant release every 3 years. 

I'd like to thank some of the contributors that have made Creusot possible, this list is not exhaustive:
- Yusuke Matsushita (@shiatsumat)
- Sarek Skotam (@sarsko)
- Jacques-Henri Jourdan (@jhjourdan)
- Dominik Stolz (@voidc)
- David Ewert (@dewert99)
- Arnaud Golfouse (@arnaudgolfouse)
- Armaël Guéneau (@armael)

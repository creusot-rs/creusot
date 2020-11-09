# Overview of project structure

- `creusot-contracts` is the crate responsible for parsing specifications and formatting them in a manner readable by `creusot`.
- `syn`, implements a parser for the specification from a rust `TokenStream`. The fork [here](https://github.com/xldenis/syn-specs) contains the version that can parse specifications. (TODO: bring this directly into the repo, at least as a submodule).
- `creusot`, a driver for rustc which produces an MLCFG file for Why3.

# Creusot Contracts

The `creusot-contracts` crate is responsible for getting the contract information into a format suitable for `creusot` to read later on.
For the moment we choose to just pass along the contract encoded into a string.
In the future, we will perform type checking and validation on the contracts before forwarding them to `creusot`.

A `requires` or `ensures` clause is transformed into a `creusot::spec::{requires, ensures}` _annotation_.

Translating `invariant` clauses is slightly more tricky.
In MIR, annotations for everything except top-level definitions are forgotten.
To get around this, we transform `invariant` clauses into an empty closure with the invariant clause attached as an annotation.
This works for us since closures are lifted to the top level during MIR creation.
This means that in MIR, our invariant becomes a reference to a closure and we can access its annotations, recovering our original invariant clause.


# How Creusot translates crates

Creusot is implemented as a `rustc` driver, which means that it runs and hooks into a normal Rust compilation pipeline.
Notably, this means that we are always working in the context of a _crate_ rather than single file.

This means that rather than producing a single module, Creusot will produce a scope/module hierarchy for Why3.
Currently a rust module `x.y.z` is translated to `scope x .. scope y .. module z ...`.
During translation we build up a map pointing each rust module with the type and function declarations contained within.

Note: Creusot translates _every_ definition in a crate, rather than trying to lazily translate those reachable from `main`.

# Translating types

We begin by requesting every type declaration in the current crate, each of which is translated into an appropriate Why type declaration.
Struct types are translated to standard Why constructors.

# Translating functions

Creusot operates at the level of MIR, and translates all 'body owners' in the current crate.
A body owner in rustc parlance is anything with MIR code, so not just top level functions but any closures and sometimes things like constructors or drop functions.

For each body owner, we collect all attributes starting with `creusot::spec`.
If we encounter a `creusot::spec::invariant` annotation, that means we are translating a closure inserted purely for an invariant, which we don't need to translate to Why at all.
Otherwise, we collect all `requires` and `ensures` annotations, which we will then translate into a WhyML contract.

Body owners are translated into MLCFG functions.
During the translation, if we encounter an assignment with a closure on the right hand side, we look to see if it has an `invariant` annotation.
If so, that whole assignment is translated to a why `invariant` statement.

**Expand on translation itself**

# Translating specifications

To translate a specification, besides the basic syntactic transformations: (&& into /\, match into case, ==> into ->, etc...) we must adjust the variables of specification clauses.

During the compilation to MIR all variables are replaced by "locals".
So we must map the variables of the clause to the new locals in MIR.
The general approach will to close a clause over all its free variables and then apply it to the corresponding mir locals.

For example given: `fn (x: u32) -> u32` and the contract `ensures=x > 0`, we turn it into `let f x = x > 0 in f _1`.

For top-level specfication clauses we will always apply them to every argument of the function.

For `invariant` clauses which could mention local variables we must do something else.
After calculating the free variables of the clause, we look into the debug information for the function being translated.
This information contains a mapping of different locals to source variable names, depending on the syntactic scope we are in.
Using this, we can find out what local each source variable was turned into, and we can construct our new contract.


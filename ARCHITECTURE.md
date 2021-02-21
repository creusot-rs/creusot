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

Specifications are parsed and typechecked by the `pearlite` crate. The resulting pearlite term is lowered to mlcfg inside of `creusot` in the `specification` module. Before lowering we must perform one important change: Changing the names of variables to refer to the lowered MIR name. The names that creusot operates with are not necessarily the same as those of source rust, so we must map source names into these resulting names. 

Additionally, we gather the variables which are accessible by a `requires`, `ensures` or `invariant` clause for typechecking. This is especially challenging in the case of an invariant clause. For this reason we use debug information to figure out which names should be in scope at that point. 

We also further desugar some pearlite terms at this point though this is relatively minor. 

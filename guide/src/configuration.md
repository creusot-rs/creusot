# Configuration

## Why3find

`cargo creusot prove` invokes `why3find`, which looks for the file `why3find.json` in the current working directory or one of its parents.
At the moment we recommend not modifying `why3find.json`. Instead, you should rely on adapting your Rust code to make proofs more robust, for example by adding more assertions.
Please open an issue if this configuration does not work for you.

Nevertheless, you may like to experiment with some of these options:

- `"fast"` and `"time"`: timeout durations in seconds for provers.
- `"depth"`: proof search is pruned after this number of levels.
- `"tactics"`: list of tactics to apply during proof search.
  "Tactics" are [Why3 transformations](https://www.why3.org/doc/technical.html#transformations) that take no arguments.
  For example: `compute_in_goal` and `inline_goal` are tactics; `apply H`, `exists X` are not tactics.

See [the Why3find README](https://git.frama-c.com/pub/why3find#why3find) for more information.

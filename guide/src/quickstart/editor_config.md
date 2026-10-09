The following configuration integrates Creusot with rust-analyzer,
enabling these features:

1. Typecheck Pearlite code (contracts, etc.) on save (see `check.overrideCommand` below).
2. Go-to-definition in Pearlite (see `cargo.extraEnv` below).

For VS Code users, you can write the following settings
in the `.vscode/settings.json` file at the root of your project:

```json
{
  "rust-analyzer.check.overrideCommand": [
    "cargo",
    "creusot",
    "--only=coma",
    "--",
    "--message-format=json"
  ],
  "rust-analyzer.cargo.extraEnv": {
    "RUSTUP_TOOLCHAIN": "{{#include ../toolchain.txt}}",
    "RUSTFLAGS": "--cfg creusot --cfg feature=\"creusot\""
  }
}
```

> [!IMPORTANT]
> The `cargo.extraEnv` entry assumes that you are using rustup to manage your Rust installation.
> In particular, this does not work for Nix users.
>
> The `RUSTUP_TOOLCHAIN` entry should contain the nightly toolchain used by Creusot.
> It is shown by the command `cargo creusot version`.

For other editors, see <https://rust-analyzer.github.io/book/other_editors.html> to add the above option to your configuration.

Note that you will probably want to enable this option _only_ in projects that use creusot.

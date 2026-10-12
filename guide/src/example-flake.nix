{
  inputs = {
    # Both `nixpkgs` and `flake-parts` are pinned to the same version as Creusot's
    nixpkgs.follows = "creusot/nixpkgs";
    flake-parts.follows = "creusot/flake-parts";

    creusot.url = "github:creusot-rs/creusot";
  };

  outputs =
    inputs@{
      creusot,
      flake-parts,
      nixpkgs,
      self,
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "aarch64-darwin"
        "x86_64-linux"
      ];

      perSystem =
        {
          pkgs,
          system,
          ...
        }:
        {
          # `pkgs` will also contain the `creusot` set, thanks to Creusot's overlay
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ creusot.overlays.default ];
          };

          # `nix fmt`
          formatter = pkgs.nixfmt-tree;

          # `nix develop`
          devShells.default = pkgs.mkShell {
            packages = [
              # `mkCreusotWrapped` produces a wrapped version of Creusot, along with all its dependencies (similar to `clang`).
              (pkgs.creusot.mkCreusotWrapped { 
                # Switch between free and non-free version of the prover `alt-ergo`.
                isFree = true;

                # `cargo` to be wrapped. By default, `cargo` needed to build Creusot is used.
                cargo = pkgs.cargo;

                # `rust-analyzer` to be wrapped. By default, `null` and no `rust-analyzer` is provided.
                rust-analyzer = pkgs.rust-analyzer-unwrapped;
              })

              # Further packages could be added
              pkgs.clippy
              pkgs.rustfmt
              # ...
            ];
          };
        };
    };
}

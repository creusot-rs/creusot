{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-26.05";
    flake-parts.url = "github:hercules-ci/flake-parts";

    crane.url = "github:ipetkov/crane";

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    inputs@{
      crane,
      flake-parts,
      nixpkgs,
      rust-overlay,
      self,
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "aarch64-darwin"
        "x86_64-linux"
      ];

      flake =
        let
          creusotAttrs = with nixpkgs.lib; {
            meta = {
              homepage = "https://github.com/creusot-rs/creusot";
              license = licenses.lgpl2;
            };

            toolchain = (importTOML ./rust-toolchain).toolchain;
            version = (importTOML ./Cargo.toml).workspace.package.version;
          };

          pins = {
            why3 = {
              version = "54c92f96bb0711d6e991c18f10bfbc08d90d028b";
              sha256 = "sha256-xLV6WQSsT1K4FQKMut4DZUAnCoL3XhKhyuPUmk+NWoE=";
            };

            why3find = {
              version = "eab37557d3e24e1913a3c4f44bc5528ef497c6c9";
              sha256 = "sha256-nyf/d3d0y5WuH5fTz93HkCbziwN0WR7sAzas+Ipauwg=";
            };

            alt-ergo = {
              version = "2.6.2";
              sha256 = "sha256-OeLJEop9HonzMuMaJxbzWfO54akl/oHxH6SnSbXSTYI=";
            };

            alt-ergo-free = {
              version = "2.4.3";
              sha256 = "sha256-ksVP9HH9pY+T6Es/wgC9pGd805AGw1e1vgfVlNGCXG8=";
            };

            cvc4 = {
              version = "1.8";
              sha256 = "sha256-V6KShPLW6kFBJaNgqy98rjOxULmf5c8AmDwo9fclGuY=";
            };

            cvc5 = {
              version = "1.3.1";
              sha256 = "sha256-nxJjrpWZfYPuuKN4CWxOHEuou4r+MdK0AjdEPZHZbHI=";
            };

            z3 = {
              version = "4.15.3";
              sha256 = "sha256-Lw037Z0t0ySxkgMXkbjNW5CB4QQLRrrSEBsLJqiomZ4=";
            };
          };
        in
        {
          overlays = rec {
            deps = import ./nix/deps pins;
            creusot = import ./nix/creusot (creusotAttrs // { inherit crane; });

            default = nixpkgs.lib.composeManyExtensions [
              rust-overlay.overlays.default
              self.overlays.deps
              self.overlays.creusot
            ];
          };
        };

      perSystem =
        {
          pkgs,
          system,
          ...
        }:
        {
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };

          formatter = pkgs.nixfmt-tree;

          packages =
            let
              rustShellToolchain = pkgs.creusot.mkRustToolchain [ ];

              mkCreusot =
                isFree:
                (pkgs.creusot.mkCreusotWrapped isFree).override (old: {
                  paths = old.paths ++ [
                    pkgs.gcc
                    rustShellToolchain
                  ];
                });
            in
            {
              inherit (pkgs.creusot) prelude creusot;

              default = mkCreusot { isFree = false; };
              free = mkCreusot { isFree = true; };
            };

          devShells =
            let
              rustDevToolchain = pkgs.creusot.mkRustToolchain (
                pkgs.creusot.components
                ++ [
                  "clippy"
                  "rust-analyzer"
                  "rust-src"
                  "rustfmt"
                ]
              );

              mkDevShell =
                isFree:
                pkgs.mkShell {
                  inputsFrom = [ pkgs.creusot.creusot ];

                  packages = [
                    (pkgs.creusot.mkWhy3Framework isFree)
                    rustDevToolchain
                  ];

                  CREUSOT_DATA_HOME = pkgs.creusot.mkWhy3Framework isFree;
                  LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [ rustDevToolchain ];
                  DYLD_FALLBACK_LIBRARY_PATH = pkgs.lib.makeLibraryPath [ rustDevToolchain ];
                };
            in
            {
              default = mkDevShell { isFree = false; };
              free = mkDevShell { isFree = true; };
            };
        };
    };
}

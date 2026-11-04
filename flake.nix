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
        "aarch64-linux"
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
              version = "05bf4ddf55cb3042f34c3bc0ed3aff56a226978a";
              sha256 = "sha256-/ISuF95qeeolPLfflq/Y5OrlYqmbQzeaTPXRLvpwG5I=";
            };

            why3find = {
              version = "9f284109620b65e6ba09e9125b598a0b26d4e4fc";
              sha256 = "sha256-MwgXNKPqChv1rR2QqW0iqVQ7+Bn2seJZnbqq+IT6qdI=";
            };

            alt-ergo = {
              version = "2.6.4";
              sha256 = "sha256-w1tbSewoFqJMkyWwg+7+I3g566zrgzMa7vBBvtcgsTc=";
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
              version = "1.4.1";
              sha256 = "sha256-LVPNGt1DKkqQ9uesKBXMtQ3t58yvtYtvyfuZnhXbIgs=";
            };

            z3 = {
              version = "5.3.2";
              sha256 = "sha256-vKNrsm09LGu8pgkX5Yv0XlY3u/MAawoma3BIeavS8So=";
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

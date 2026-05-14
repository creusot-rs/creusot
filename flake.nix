{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.11";
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
              version = "2c0f2992af85f82f3eda0f158dcf10e62e0db875";
              sha256 = "sha256-9ReUqizS2Jmh2qqRmnygKmFCTaHrpvMGg+wiwrhONiE=";
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
        let
          rust =
            let
              inherit ((pkgs.lib.importTOML ./rust-toolchain).toolchain) channel components;

              devComponents = [
                "clippy"
                "rust-analyzer"
                "rust-src"
                "rustfmt"
              ];

              mkRustToolchain =
                components:
                let
                  toolchain = {
                    inherit channel components;
                    profile = "minimal";
                  };
                in
                pkgs.rust-bin.fromRustupToolchain toolchain;
            in
            {
              lib = crane.mkLib pkgs;

              toolchain = {
                build = mkRustToolchain components;
                dev = mkRustToolchain (components ++ devComponents);
              };
            };

          mkWhy3Framework =
            {
              isFree,
            }:
            let
              solvers =
                with pkgs.creusot;
                let
                  solvers = if isFree then [ alt-ergo-free ] else [ alt-ergo ];
                in
                [
                  cvc4
                  cvc5
                  why3
                  why3find
                  z3
                ]
                ++ solvers;

              why3json = pkgs.writeTextFile {
                destination = "/why3find.json";
                name = "why3find.json";
                text = builtins.readFile ./why3find.json;
              };
            in
            pkgs.symlinkJoin {
              name = "creusot-why3";
              paths = solvers ++ [ why3json ];
              postBuild = "ln -s $out $out/creusot";

              passthru = builtins.listToAttrs (
                map (drv: {
                  name = drv.pname;
                  value = drv;
                }) solvers
              );
            };
        in
        {
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };

          packages = {
            inherit (pkgs.creusot) prelude creusot;
          }
          // (
            let
              mkEnv =
                isFree:
                pkgs.buildEnv {
                  name = "creusot-env";
                  paths = [
                    pkgs.creusot.creusot
                    pkgs.creusot.prelude
                    pkgs.gcc
                    rust.toolchain.build
                    (mkWhy3Framework isFree)
                  ];

                  nativeBuildInputs = [ pkgs.makeWrapper ];
                  postBuild = ''
                    wrapProgram $out/bin/cargo-creusot \
                      --set CREUSOT_DATA_HOME "$out"
                  '';
                };

            in
            {
              default = mkEnv { isFree = false; };
              free = mkEnv { isFree = true; };
            }
          );

          devShells =
            let
              mkShell =
                isFree:
                pkgs.mkShell {
                  inputsFrom = [ pkgs.creusot.creusot ];
                  packages = [
                    rust.toolchain.dev
                    (mkWhy3Framework isFree)
                  ];

                  CREUSOT_DATA_HOME = mkWhy3Framework isFree;
                  LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [ rust.toolchain.dev ];
                  DYLD_FALLBACK_LIBRARY_PATH = pkgs.lib.makeLibraryPath [ rust.toolchain.dev ];

                  passthru = rust.toolchain.dev.passthru.availableComponents;
                };
            in
            {
              default = mkShell { isFree = false; };
              free = mkShell { isFree = true; };
            };

          formatter = pkgs.nixfmt-tree;
        };
    };
}

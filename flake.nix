{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-25.11";
    flake-utils.url = "github:numtide/flake-utils";

    crane.url = "github:ipetkov/crane";

    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    crane,
    flake-utils,
    nixpkgs,
    rust-overlay,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      lib = nixpkgs.lib.extend (_: _: (import ./nix {
        inherit pins pkgs;
      }));

      overlays = [
        rust-overlay.overlays.default
        (super: self: {
          ocamlPackages = self.ocamlPackages.overrideScope (
            final: _: {
              ocplib-simplex_0_4 = final.callPackage ./nix/pkgs/ocplib-simplex.nix {};
            }
          );
          alt-ergo-free = self.callPackage ./nix/pkgs/alt-ergo-free.nix {};
        })
      ];
      pkgs = import nixpkgs {inherit overlays system;};

      pins = {
        why3 = {
          version = "2c0f2992af85f82f3eda0f158dcf10e62e0db875";
          sha256 = "sha256-9ReUqizS2Jmh2qqRmnygKmFCTaHrpvMGg+wiwrhONiE=";
        };

        why3find = {
          version = "eab37557d3e24e1913a3c4f44bc5528ef497c6c9";
          sha256 = "sha256-nyf/d3d0y5WuH5fTz93HkCbziwN0WR7sAzas+Ipauwg=";
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

        creusot = {
          inherit ((pkgs.lib.importTOML ./Cargo.toml).workspace.package) version;

          meta = with pkgs.lib; {
            homepage = "https://github.com/creusot-rs/creusot";
            license = licenses.lgpl2;
          };
        };
      };

      rust = let
        inherit ((pkgs.lib.importTOML ./rust-toolchain).toolchain) channel components;
        devComponents = ["clippy" "rust-analyzer" "rust-src" "rustfmt"];

        mkRustToolchain = components: let
          toolchain = {
            inherit channel components;
            profile = "minimal";
          };
        in
          pkgs.rust-bin.fromRustupToolchain toolchain;
      in {
        lib = crane.mkLib pkgs;

        toolchain = {
          build = mkRustToolchain components;
          dev = mkRustToolchain (components ++ devComponents);
        };

        envBuilder = rust.lib.overrideToolchain rust.toolchain.build;
      };
    in rec {
      inherit lib;

      packages = let
        src = pkgs.lib.cleanSourceWith {
          name = "creusot-source";
          src = ./.;

          filter = path: type:
            (rust.lib.filterCargoSources path type)
            || (builtins.match ".*/rust-toolchain" path != null)
            || (builtins.match ".*/messages.ftl" path != null)
            || (builtins.match ".*/*.coma" path != null)
            || (builtins.match ".*/*.json" path != null)
            || (builtins.match ".*/*.stderr" path != null);
        };
      in {
        why3Framework = let
          solvers = with lib.pkgs; [alt-ergo-free cvc4 cvc5 why3 why3find z3];

          why3json = pkgs.writeTextFile {
            destination = "/why3find.json";
            name = "why3find.json";
            text = builtins.readFile ./why3find.json;
          };
        in
          pkgs.symlinkJoin {
            name = "creusot-why3";
            paths = solvers ++ [why3json];
            postBuild = "ln -s $out $out/creusot";

            passthru = builtins.listToAttrs (map (drv: {
                name = drv.pname;
                value = drv;
              })
              solvers);
          };

        prelude = let
          inherit (pins.creusot) meta version;
          inherit src;

          pname = "prelude-generator";
          cargoExtraArgs = "--bin prelude-generator";

          cargoArtifacts = rust.envBuilder.buildDepsOnly {
            inherit (pins.creusot) meta version;
            inherit cargoExtraArgs pname src;
          };

          preludeBinary = rust.envBuilder.buildPackage {
            inherit cargoArtifacts cargoExtraArgs meta pname src version;

            nativeBuildInputs = with pkgs;
              lib.optionals stdenv.isDarwin [libiconv libzip];
          };
        in
          pkgs.runCommand "prelude" {
            nativeBuildInputs = [preludeBinary];
          } ''
            mkdir -p $out/share/why3find ./prelude-generator ./target/creusot
            cp ${src}/prelude-generator/*.coma ./prelude-generator

            CARGO_MANIFEST_DIR=./target ${preludeBinary}/bin/prelude-generator

            cp -r ./target/creusot/packages $out/share/why3find/.
          '';

        creusot = let
          inherit (pins.creusot) meta version;

          pname = "cargo-creusot";
          cargoExtraArgs = "--workspace --exclude creusot-install --exclude prelude-generator";
        in
          rust.envBuilder.buildPackage rec {
            inherit cargoExtraArgs meta pname src version;

            nativeBuildInputs = with pkgs;
              [makeWrapper]
              ++ lib.optionals stdenv.isDarwin [libiconv libzip];

            cargoArtifacts = rust.envBuilder.buildDepsOnly {
              inherit cargoExtraArgs meta pname src version;
            };

            doNotRemoveReferencesToRustToolchain = true;

            postInstall = with lib.strings; ''
              mkdir $out/share
              cp {Cargo.toml,Cargo.lock} $out/share/.
              cp -r {creusot-std,creusot-std-proc,pearlite-syn} $out/share/.

              wrapProgram $out/bin/cargo-creusot \
                --set CREUSOT_STD $out/share/creusot-std \
                --set CREUSOT_RUSTC $out/bin/creusot-rustc \

              wrapProgram $out/bin/creusot-rustc \
                --set LD_LIBRARY_PATH "${makeLibraryPath [rust.toolchain.build]}" \
                --set DYLD_FALLBACK_LIBRARY_PATH "${makeLibraryPath [rust.toolchain.build]}"
            '';
          };

        default = pkgs.buildEnv {
          name = "creusot-env";
          paths =
            [pkgs.gcc rust.toolchain.build]
            ++ (with packages; [creusot prelude why3Framework]);

          nativeBuildInputs = [pkgs.makeWrapper];
          postBuild = ''
            wrapProgram $out/bin/cargo-creusot \
              --set CREUSOT_DATA_HOME "$out"
          '';
        };
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = [packages.creusot];
        packages = [packages.why3Framework rust.toolchain.dev];

        CREUSOT_DATA_HOME = packages.why3Framework;
        LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [rust.toolchain.dev];
        DYLD_FALLBACK_LIBRARY_PATH = pkgs.lib.makeLibraryPath [rust.toolchain.dev];

        passthru = rust.toolchain.dev.passthru.availableComponents;
      };

      formatter = pkgs.alejandra;
    });
}

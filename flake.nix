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

      overlays = [rust-overlay.overlays.default];
      pkgs = import nixpkgs {inherit overlays system;};

      pins = {
        why3 = {
          version = "51e0579b3561f51a305069042dd9fba56154e600";
          sha256 = "sha256-KNna+AEDwvc9AWWLiyTbofk2lAwa99Z/9d443McfG9c=";
        };

        why3find = {
          version = "833defb466008b37511bb503e671704b8ce2b192";
          sha256 = "sha256-h0YzvsQ6s+Z6ImHXlKa856gDRE1ZsEP8T+ztdg5Rsiw=";
        };

        alt-ergo = {
          version = "2.6.2";
          sha256 = "sha256-OeLJEop9HonzMuMaJxbzWfO54akl/oHxH6SnSbXSTYI=";
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
          licence = {
            gpl = with lib.pkgs; [cvc4 cvc5 why3 why3find z3];
            unfree = licence.gpl ++ (with lib.pkgs; [alt-ergo]);
          };

          why3json = pkgs.writeTextFile {
            destination = "/why3find.json";
            name = "why3find.json";
            text = builtins.readFile ./why3find.json;
          };
        in
          pkgs.symlinkJoin {
            name = "creusot-why3";
            paths = licence.unfree ++ [why3json];
            postBuild = "ln -s $out $out/creusot";
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
            mkdir -p $out/share/why3find/packages/creusot/creusot ./prelude-generator ./target/creusot
            cp ${src}/why3find.json .
            cp ${src}/prelude-generator/*.coma ./prelude-generator

            CARGO_MANIFEST_DIR=./target ${preludeBinary}/bin/prelude-generator

            cp ./target/creusot/*.coma $out/share/why3find/packages/creusot/creusot
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
              cp -r {creusot-contracts,creusot-contracts-proc,pearlite-syn} $out/share/.

              wrapProgram $out/bin/cargo-creusot \
                --set CREUSOT_CONTRACTS $out/share/creusot-contracts \
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

        CREUSOT_DATA_HOME = pkgs.buildEnv {
          name = "creusot-env";
          paths = (with packages; [prelude why3Framework]);
        };

        LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [rust.toolchain.dev];
        DYLD_FALLBACK_LIBRARY_PATH = pkgs.lib.makeLibraryPath [rust.toolchain.dev];

        passthru = {
          toolchain = rust.toolchain.dev;
        };
      };

      formatter = pkgs.alejandra;
    });
}

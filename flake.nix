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

      tools = {
        gpl = with lib.pkgs; [cvc4 cvc5 why3 why3find z3];
        unfree = tools.gpl ++ (with lib.pkgs; [alt-ergo]);
      };

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
          version = "0.7.0";

          meta = with pkgs.lib; {
            homepage = "https://github.com/creusot-rs/creusot";
            license = licenses.lgpl2;
          };
        };
      };

      rust = let
        rustToolchain = (pkgs.lib.importTOML ./rust-toolchain).toolchain;
      in {
        lib = crane.mkLib pkgs;

        toolchain = pkgs.rust-bin.fromRustupToolchain rustToolchain;
        env = rust.lib.overrideToolchain rust.toolchain;
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
            || (builtins.match ".*/*.json" path != null);
        };
      in {
        tools = let
          why3json = pkgs.writeTextFile {
            destination = "/why3find.json";
            name = "why3find.json";
            text = builtins.readFile ./why3find.json;
          };
        in
          pkgs.symlinkJoin {
            name = "creusot-tools";
            paths = tools.unfree ++ [why3json];
            postBuild = "ln -s $out $out/creusot";
          };

        prelude = let
          inherit (pins.creusot) meta version;
          inherit src;

          pname = "prelude-generator";
          cargoExtraArgs = "--bin prelude-generator";

          cargoArtifacts = rust.env.buildDepsOnly {
            inherit (pins.creusot) meta version;
            inherit cargoExtraArgs pname src;
          };

          preludeBinary = rust.env.buildPackage {
            inherit cargoArtifacts cargoExtraArgs meta pname src version;

            buildInputs = [rust.toolchain];
            nativeBuildInputs = with pkgs;
              lib.optionals stdenv.isDarwin [libiconv libzip];

            doCheck = false;
          };
        in
          pkgs.runCommand "prelude" {
            nativeBuildInputs = [preludeBinary];
          } ''
            mkdir -p $out/{creusot,prelude-generator,target/creusot}
            cp ${src}/why3find.json $out
            find ${src}/prelude-generator -name "*.coma" -exec cp {} $out/prelude-generator \;

            CARGO_MANIFEST_DIR=$out/target ${preludeBinary}/bin/prelude-generator
            find $out/target -name "*.coma" -exec mv {} $out/creusot \;
            rm -rf $out/prelude-generator $out/target $out/why3find.json
          '';

        creusot = let
          inherit (pins.creusot) meta version;

          pname = "cargo-creusot";
          cargoExtraArgs = "--workspace --exclude creusot-install --exclude prelude-generator";
        in
          rust.env.buildPackage rec {
            inherit cargoExtraArgs meta pname src version;

            buildInputs = [rust.toolchain];
            nativeBuildInputs = with pkgs;
              [makeWrapper]
              ++ lib.optionals stdenv.isDarwin [libiconv libzip];

            cargoArtifacts = rust.env.buildDepsOnly {
              inherit cargoExtraArgs meta pname src version;
            };

            doCheck = false;
            doNotRemoveReferencesToRustToolchain = true;

            postInstall = with lib.strings; ''
              mkdir $out/share
              cp {Cargo.toml,Cargo.lock} $out/share/.
              cp -r {creusot-contracts,creusot-contracts-proc,pearlite-syn} $out/share/.

              wrapProgram $out/bin/cargo-creusot \
                --set CREUSOT_CONTRACTS $out/share/creusot-contracts \
                --set CREUSOT_RUSTC $out/bin/creusot-rustc \

              wrapProgram $out/bin/creusot-rustc \
                --set LD_LIBRARY_PATH "${makeLibraryPath [rust.toolchain]}" \
                --set DYLD_FALLBACK_LIBRARY_PATH "${makeLibraryPath [rust.toolchain]}"
            '';
          };

        default = pkgs.buildEnv {
          name = "creusot-env";
          paths = [pkgs.gcc packages.creusot packages.tools rust.toolchain];

          nativeBuildInputs = [pkgs.makeWrapper];
          postBuild = ''
            wrapProgram $out/bin/cargo-creusot \
              --set CREUSOT_DATA_HOME "${packages.tools}" \
              --set CREUSOT_PRELUDE "${packages.prelude}"
          '';
        };
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = [packages.creusot];
        packages = [packages.tools];

        CREUSOT_DATA_HOME = packages.tools;
        LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [rust.toolchain];
        DYLD_FALLBACK_LIBRARY_PATH = pkgs.lib.makeLibraryPath [rust.toolchain];
      };

      formatter = pkgs.alejandra;
    });
}

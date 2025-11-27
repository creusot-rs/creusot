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
          version = "1.8.2";
          sha256 = "sha256-t9ES7dW8zmvM4AI9K8g06yrhocQteupE/6Ek1km1C+o=";
        };

        why3find = {
          version = "1.2.0";
          sha256 = "sha256-qUeT5jVDlpNTuQFTlMZlHJ/RSOXbDDEDFzO5kBpvS1g=";
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
        toolchain = pkgs.rust-bin.fromRustupToolchain rustToolchain;
        env = (crane.mkLib pkgs).overrideToolchain rust.toolchain;
      };
    in rec {
      inherit lib;

      packages = {
        tools = pkgs.symlinkJoin {
          name = "creusot-tools";
          paths = tools.unfree;
          postBuild = "ln -s $out $out/creusot";
        };

        creusot = let
          inherit (pins.creusot) meta version;

          src = ./.;
          pname = "cargo-creusot";

          cargoExtraArgs = "--workspace --exclude creusot-install";
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

            doNotRemoveReferencesToRustToolchain = true;

            postInstall = with lib.strings; ''
              wrapProgram $out/bin/cargo-creusot \
                --append-flags "--creusot-rustc $out/bin/creusot-rustc" \
                --set XDG_DATA_HOME "${packages.tools}"

              wrapProgram $out/bin/creusot-rustc \
                --set LD_LIBRARY_PATH "${makeLibraryPath [rust.toolchain]}" \
                --set DYLD_FALLBACK_LIBRARY_PATH "${makeLibraryPath [rust.toolchain]}"
            '';
          };

        default = pkgs.symlinkJoin {
          name = "creusot-env";
          paths = [packages.creusot packages.tools rust.toolchain];
        };
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = [packages.creusot];
        packages = [packages.tools];

        LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [rust.toolchain];
        DYLD_FALLBACK_LIBRARY_PATH = pkgs.lib.makeLibraryPath [rust.toolchain];
        XDG_DATA_HOME = packages.tools;
      };

      formatter = pkgs.alejandra;
    });
}

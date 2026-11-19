attrs: final: prev:
let
  manifest = builtins.fromTOML (builtins.readFile ../../Cargo.toml);
  mkSource =
    members:
    let
      cargoToml = (final.formats.toml { }).generate "Cargo.toml" (
        manifest
        // {
          workspace = manifest.workspace // {
            inherit members;
          };
        }
      );
    in
    {
      src = final.lib.fileset.toSource {
        root = ../..;
        fileset = final.lib.fileset.unions (
          [
            ../../Cargo.lock
            ../../rust-toolchain
          ]
          ++ map (member: ../.. + "/${member}") members
        );
      };

      postUnpack = ''
        cp ${cargoToml} "$sourceRoot/Cargo.toml"
      '';
    };

  mkRustToolchain =
    components:
    final.rust-bin.fromRustupToolchain {
      inherit (attrs.toolchain) channel;
      inherit components;

      profile = "minimal";
    };

  rustLib = attrs.crane.mkLib final;
  rustToolchain = mkRustToolchain attrs.toolchain.components;
  rustBuilder = rustLib.overrideToolchain rustToolchain;
in
{
  creusot = prev.creusot or { } // {
    inherit (attrs.toolchain) components;
    inherit mkRustToolchain;

    prelude = final.callPackage ./prelude.nix {
      inherit (attrs) meta version;
      inherit (mkSource [ "prelude-generator" ]) src postUnpack;
      inherit rustBuilder;
    };

    creusot =
      let
        members = builtins.filter (
          member:
          !builtins.elem member [
            "creusot-install"
            "prelude-generator"
            "tests"
          ]
        ) manifest.workspace.members;
      in
      final.callPackage ./creusot.nix {
        inherit (attrs) meta version;
        inherit (mkSource members) src postUnpack;
        inherit rustBuilder rustToolchain;
      };

    mkWhy3Framework = final.callPackage ./mkWhy3Framework.nix { };
    mkCreusotWrapped = final.callPackage ./mkCreusotWrapped.nix {
      inherit rustToolchain;
    };
  };
}

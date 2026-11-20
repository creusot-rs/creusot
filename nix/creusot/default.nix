attrs: final: prev:
let
  manifest = builtins.fromTOML (builtins.readFile ../../Cargo.toml);
  mkSource =
    {
      members,
      extraPaths ? [ ],
    }:
    let
      cargoToml = (final.formats.toml { }).generate "Cargo.toml" (
        manifest
        // {
          workspace = manifest.workspace // {
            inherit members;
            lints.cargo.unused_workspace_package_fields = "allow";
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
          ++ map (path: ../.. + "/${path}") extraPaths
        );
      };

      postUnpack = ''
        cp ${cargoToml} "$sourceRoot/Cargo.toml"

        for manifest in "$sourceRoot"/*/Cargo.toml; do
          echo '[lints.cargo]' >> "$manifest"
          echo 'unused_dependencies = "allow"' >> "$manifest"
        done
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
    inherit mkRustToolchain rustBuilder;

    prelude = final.callPackage ./prelude.nix {
      inherit (attrs) meta version;
      inherit (mkSource { members = [ "prelude-generator" ]; }) src postUnpack;
      inherit rustBuilder;
    };

    creusot =
      let
        excludedMembers = [
          "creusot-install"
          "prelude-generator"
          "tests"
        ];

        members = builtins.filter (
          member: !builtins.elem member excludedMembers
        ) manifest.workspace.members;
      in
      final.callPackage ./creusot.nix {
        inherit (attrs) meta version;
        inherit (mkSource { inherit members; }) src postUnpack;
        inherit rustBuilder rustToolchain;

        check =
          let
            attrs = {
              members = members ++ [ "tests" ];
              extraPaths = [ "examples" ];
            };
          in
          {
            inherit (mkSource attrs) src postUnpack;
          };
      };

    mkWhy3Framework = final.callPackage ./mkWhy3Framework.nix { };
    mkCreusotWrapped = final.callPackage ./mkCreusotWrapped.nix {
      inherit rustToolchain;
    };
  };
}

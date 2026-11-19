attrs: final: prev:
let
  rustLib = attrs.crane.mkLib final;

  src = final.lib.cleanSourceWith {
    name = "creusot-source";
    src = ../..;

    filter =
      path: type:
      let
        filename = baseNameOf path;
      in
      final.lib.cleanSourceFilter path type
      || rustLib.filterCargoSources path type
      || builtins.elem filename [ "rust-toolchain" "messages.ftl" ]
      || final.lib.hasSuffix ".coma" filename
      || final.lib.hasSuffix ".json" filename
      || final.lib.hasSuffix ".stderr" filename;
  };

  mkRustToolchain =
    components:
    final.rust-bin.fromRustupToolchain {
      inherit (attrs.toolchain) channel;
      inherit components;

      profile = "minimal";
    };

  rustToolchain = mkRustToolchain attrs.toolchain.components;
  rustBuilder = rustLib.overrideToolchain rustToolchain;
in
{
  creusot = prev.creusot or { } // {
    inherit (attrs.toolchain) components;
    inherit mkRustToolchain;

    prelude = final.callPackage ./prelude.nix {
      inherit (attrs) meta version;
      inherit rustBuilder;
    };

    creusot = final.callPackage ./creusot.nix {
      inherit (attrs) meta version;
      inherit rustBuilder rustToolchain src;
    };

    mkWhy3Framework = final.callPackage ./mkWhy3Framework.nix { };
    mkCreusotWrapped = final.callPackage ./mkCreusotWrapped.nix {
      inherit rustToolchain;
    };
  };
}

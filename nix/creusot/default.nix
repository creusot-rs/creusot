attrs: final: prev:
let
  rustLib = attrs.crane.mkLib final;

  src = final.lib.cleanSourceWith {
    name = "creusot-source";
    src = ../..;

    filter =
      path: type:
      (rustLib.filterCargoSources path type)
      || (builtins.match ".*/rust-toolchain" path != null)
      || (builtins.match ".*/messages.ftl" path != null)
      || (builtins.match ".*/.*\.coma" path != null)
      || (builtins.match ".*/.*\.json" path != null)
      || (builtins.match ".*/.*\.stderr" path != null);
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
      inherit rustBuilder src;
    };

    creusot = final.callPackage ./creusot.nix {
      inherit (attrs) meta version;
      inherit rustBuilder rustToolchain src;
    };

    mkWhy3Framework = final.callPackage ./mkWhy3Framework.nix {};
    mkCreusotShell = final.callPackage ./mkCreusotShell.nix {
      inherit rustToolchain;
    };
  };
}

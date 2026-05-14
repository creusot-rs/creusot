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

  toolchain = final.rust-bin.fromRustupToolchain attrs.toolchain;
  envBuilder = rustLib.overrideToolchain toolchain;
in
{
  creusot = prev.creusot or { } // {
    prelude = final.callPackage ./prelude.nix {
      inherit (attrs) meta version;
      inherit envBuilder src;
    };

    creusot = final.callPackage ./creusot.nix {
      inherit (attrs) meta version;
      inherit envBuilder src toolchain;
    };
  };
}

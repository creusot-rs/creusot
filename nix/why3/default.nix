pins: final: prev:
let
  callPackage = final.lib.callPackageWith (final // why3Framework);

  why3Framework = prev.why3Framework or { } // {
    inherit callPackage;

    # Why3 toolchain
    why3 = callPackage ./why3.nix (pins.why3 // { inherit (prev) why3; });
    why3find = callPackage ./why3find.nix pins.why3find;

    # Alt-Ergo
    alt-ergo = callPackage ./alt-ergo.nix (pins.alt-ergo // { inherit (prev) alt-ergo; });
    alt-ergo-free = callPackage ./alt-ergo-free.nix (
      pins.alt-ergo-free // { inherit (prev) alt-ergo-free; }
    );

    # CVC4 and CVC5
    cocoalib = callPackage ./cocoalib.nix { };
    cryptominisat = callPackage ./cryptominisat.nix { inherit (prev) cryptominisat; };
    glpk = callPackage ./glpk.nix { inherit (prev) glpk; };
    libpoly = callPackage ./libpoly.nix { inherit (prev) libpoly; };
    symfpu = callPackage ./symfpu.nix { inherit (prev) symfpu; };

    cvc4 = callPackage ./cvc4.nix (pins.cvc4 // { inherit (prev) cvc4; });
    cvc5 = callPackage ./cvc5.nix (
      pins.cvc5
      // {
        inherit (prev) cvc5;
        cadical = final.cadical.override { version = "2.1.3"; };
      }
    );

    # Z3
    z3 = callPackage ./z3.nix (pins.z3 // { inherit (prev) z3; });
  };
in
{
  inherit why3Framework;
}

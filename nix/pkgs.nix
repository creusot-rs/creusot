pins: final: prev: {
  alt-ergo = final.callPackage ./alt-ergo.nix (pins.alt-ergo // { inherit (prev) alt-ergo; });
  alt-ergo-free = final.callPackage ./alt-ergo-free.nix pins.alt-ergo-free;

  cvc4 = final.callPackage ./cvc4.nix (pins.cvc4 // { inherit (prev) cvc4; });
  cvc5 = final.callPackage ./cvc5.nix (pins.cvc5 // { inherit (prev) cvc5; });

  why3 = final.callPackage ./why3.nix (pins.why3 // { inherit (prev) why3; });
  why3find = final.callPackage ./why3find.nix pins.why3find;

  z3 = final.callPackage ./z3.nix (pins.z3 // { inherit (prev) z3; });
}

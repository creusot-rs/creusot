{
  pkgs,
  pins,
}: {
  pkgs = rec {
    alt-ergo = import ./alt-ergo.nix ({inherit pkgs;} // pins.alt-ergo);
    cvc4 = import ./cvc4.nix ({inherit pkgs;} // pins.cvc4);
    cvc5 = import ./cvc5.nix ({inherit pkgs;} // pins.cvc5);
    why3 = import ./why3.nix ({inherit pkgs;} // pins.why3);
    why3find = import ./why3find.nix ({inherit pkgs why3;} // pins.why3find);
    z3 = import ./z3.nix ({inherit pkgs;} // pins.z3);
  };
}

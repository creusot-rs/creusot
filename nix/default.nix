{
  nixpkgs,
  overlays,
  pins,
  system,
}: rec {
  pkgs = import nixpkgs {
    inherit system;

    overlays = overlays ++ [
      (import ./cvc-deps.nix)
      (import ./cvc4.nix pins.cvc4)
      (import ./cvc5.nix pins.cvc5)
    ];
  };

  creusotPkgs = rec {
    alt-ergo = import ./alt-ergo.nix ({inherit pkgs;} // pins.alt-ergo);
    why3 = import ./why3.nix ({inherit pkgs;} // pins.why3);
    why3find = import ./why3find.nix ({inherit pkgs why3;} // pins.why3find);
    z3 = import ./z3.nix ({inherit pkgs;} // pins.z3);
  };
}

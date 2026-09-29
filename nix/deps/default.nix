pins: final: prev: {
  ocamlPackages = prev.ocamlPackages.overrideScope (
    _: prevOCaml: {
      dolmen = prevOCaml.dolmen.overrideAttrs (old: {
        src = prev.fetchurl {
          url = "https://github.com/Gbury/dolmen/archive/a0f1bc66e7256fff1068ac0df525a2d23c1f3ea7.tar.gz";
          hash = "sha256-ZhjBiwvoVvhkV7F6heHCQ00NkK6xJhJlMXx3YjRyp7Q=";
        };

        propagatedBuildInputs = old.propagatedBuildInputs ++ [
          prevOCaml.uutf
          prevOCaml.dune-site
        ];

        nativeBuildInputs =
          old.nativeBuildInputs
          ++ prev.lib.optionals prev.stdenv.hostPlatform.isDarwin [ prev.darwin.sigtool ];
      });

      dolmen_type = prevOCaml.dolmen_type.overrideAttrs (old: {
        src = prev.fetchurl {
          url = "https://github.com/Gbury/dolmen/archive/a0f1bc66e7256fff1068ac0df525a2d23c1f3ea7.tar.gz";
          hash = "sha256-ZhjBiwvoVvhkV7F6heHCQ00NkK6xJhJlMXx3YjRyp7Q=";
        };
      });

      dolmen_loop = prevOCaml.dolmen_loop.overrideAttrs (old: {
        src = prev.fetchurl {
          url = "https://github.com/Gbury/dolmen/archive/a0f1bc66e7256fff1068ac0df525a2d23c1f3ea7.tar.gz";
          hash = "sha256-ZhjBiwvoVvhkV7F6heHCQ00NkK6xJhJlMXx3YjRyp7Q=";
        };

        propagatedBuildInputs = old.propagatedBuildInputs ++ [ prevOCaml.zarith ];

        nativeBuildInputs =
          old.nativeBuildInputs
          ++ prev.lib.optionals prev.stdenv.hostPlatform.isDarwin [ prev.darwin.sigtool ];
      });
    }
  );

  creusot = prev.creusot or { } // {
    alt-ergo = final.callPackage ./alt-ergo.nix pins.alt-ergo;
    alt-ergo-free = final.callPackage ./alt-ergo-free.nix pins.alt-ergo-free;

    cvc4 = final.callPackage ./cvc4.nix pins.cvc4;
    cvc5 = final.callPackage ./cvc5.nix pins.cvc5;

    why3 = final.callPackage ./why3.nix pins.why3;
    why3find = final.callPackage ./why3find.nix pins.why3find;

    z3 = final.callPackage ./z3.nix pins.z3;
  };
}

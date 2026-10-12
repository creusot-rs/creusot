{
  # Dependencies
  ocamlPackages,

  # Previous overlay
  alt-ergo,

  # Librairies
  darwin,
  fetchurl,
  lib,
  stdenv,

  # Pins
  sha256,
  version,
}:

let
  pname = "alt-ergo";

  src = fetchurl {
    url = "https://github.com/OCamlPro/alt-ergo/releases/download/v${version}/alt-ergo-${version}.tbz";
    hash = sha256;
  };
in

let
  alt-ergo-lib = ocamlPackages.buildDunePackage {
    inherit version src;
    pname = "alt-ergo-lib";

    nativeBuildInputs = with ocamlPackages; [ crunch ];
    buildInputs = with ocamlPackages; [ ppx_blob ];
    propagatedBuildInputs = with ocamlPackages; [
      camlzip
      dolmen_loop
      dune-build-info
      fmt
      ocplib-simplex
      ppx_deriving
      seq
      stdlib-shims
      zarith
    ];
  };

  # NOTE: Will be deleted in the next release
  alt-ergo-parsers = ocamlPackages.buildDunePackage {
    inherit version src;
    pname = "alt-ergo-parsers";

    nativeBuildInputs = [ ocamlPackages.menhir ];
    propagatedBuildInputs = [ alt-ergo-lib ] ++ (with ocamlPackages; [ psmt2-frontend ]);
  };
in

ocamlPackages.buildDunePackage {
  inherit pname version src;
  inherit (alt-ergo) meta outputs;
  inherit (alt-ergo) installPhase nativeBuildInputs;

  propagatedBuildInputs = [
    alt-ergo-lib
    alt-ergo-parsers
  ]
  ++ (with ocamlPackages; [
    cmdliner
    dune-site
    fmt
    ppxlib
  ]);
}

{
  # Dependencies
  autoreconfHook,
  ocamlPackages,

  # Librairies
  fetchFromGitHub,
  fetchurl,
  lib,
  stdenv,

  # Pins
  sha256,
  version,
}:
let
  ocplib-simplex_0_4 = stdenv.mkDerivation rec {
    pname = "ocplib-simplex";
    version = "0.4.1";

    src = fetchFromGitHub {
      owner = "OCamlPro";
      repo = pname;
      rev = "v${version}";
      hash = "sha256-bhlTBpJg031x2lUjwuVrhQgOGmDLW/+0naN8wRjv6i4=";
    };

    nativeBuildInputs = [
      autoreconfHook
    ]
    ++ (with ocamlPackages; [
      ocaml
      findlib
    ]);

    installFlags = [ "LIBDIR=$(OCAMLFIND_DESTDIR)" ];

    createFindlibDestdir = true;
  };
in
ocamlPackages.buildDunePackage rec {
  pname = "alt-ergo-free";
  inherit version;

  src = fetchurl {
    url = "https://github.com/OCamlPro/alt-ergo/releases/download/v${version}-free/alt-ergo-${version}-free.tar.gz";
    hash = sha256;
  };

  nativeBuildInputs = [ ocamlPackages.menhir ];

  sourceRoot = ".";

  buildInputs = [
    ocplib-simplex_0_4
  ]
  ++ (with ocamlPackages; [
    cmdliner
    camlzip
    stdlib-shims
    dune-configurator
    dune-build-info
    num
    psmt2-frontend
    zarith
    seq
  ]);

  meta = {
    description = "High-performance theorem prover and SMT solver";
    homepage = "https://alt-ergo.ocamlpro.com/";
    license = lib.licenses.cecill-c;
  };
}

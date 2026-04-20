{
  pkgs,
  version,
  sha256,
}: let
  ocamlPackages = pkgs.ocamlPackages;
  ocplib-simplex_0_4 = pkgs.stdenv.mkDerivation rec {
    pname = "ocplib-simplex";
    version = "0.4.1";

    src = pkgs.fetchFromGitHub {
      owner = "OCamlPro";
      repo = pname;
      rev = "v${version}";
      hash = "sha256-bhlTBpJg031x2lUjwuVrhQgOGmDLW/+0naN8wRjv6i4=";
    };

    nativeBuildInputs =
      [pkgs.autoreconfHook]
      ++ (with ocamlPackages; [
        ocaml
        findlib
      ]);

    installFlags = ["LIBDIR=$(OCAMLFIND_DESTDIR)"];

    createFindlibDestdir = true;
  };
in
  ocamlPackages.buildDunePackage rec {
    pname = "alt-ergo-free";
    inherit version;

    src = pkgs.fetchurl {
      url = "https://github.com/OCamlPro/alt-ergo/releases/download/v${version}-free/alt-ergo-${version}-free.tar.gz";
      hash = sha256;
    };

    nativeBuildInputs = [ocamlPackages.menhir];

    sourceRoot = ".";

    buildInputs =
      [ocplib-simplex_0_4]
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
      license = pkgs.lib.licenses.cecill-c;
    };
  }

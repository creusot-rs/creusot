{
  pkgs,
  version,
  sha256,
}:
with pkgs;
with ocamlPackages;
  stdenv.mkDerivation {
    inherit (why3) installTargets meta pname postInstall outputs;
    inherit version;

    src = pkgs.fetchurl {
      url = "https://gitlab.inria.fr/why3/why3/-/archive/${version}/why3-${version}.tar.gz";
      hash = sha256;
    };

    nativeBuildInputs = [
      findlib
      menhir
      ocaml
      wrapGAppsHook3
    ];

    buildInputs = [
      autoreconfHook
      lablgtk3-sourceview3
      ocamlgraph
    ];

    propagatedBuildInputs = [
      camlzip
      menhirLib
      re
      sexplib
      zarith
    ];

    configureFlags = [
      "--enable-ide"
      "--enable-verbose-make"

      "--disable-js-of-ocaml"
      "--disable-web-ide"
      "--disable-coq-libs"
      "--disable-isabelle-libs"
      "--disable-pvs-libs"

      "--disable-doc"
      "--disable-pdf-doc"

      "--disable-emacs-compilation"
      "--disable-java"
    ];
  }

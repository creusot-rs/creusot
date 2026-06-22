{
  # Dependencies
  autoreconfHook,
  dune,
  ocaml,
  ocamlPackages,
  wrapGAppsHook3,

  # Previous overlay
  why3,

  # Librairies
  fetchurl,
  stdenv,

  # Pins
  sha256,
  version,
}:
stdenv.mkDerivation {
  inherit (why3)
    installTargets
    meta
    pname
    postInstall
    outputs
    ;
  inherit version;

  src = fetchurl {
    url = "https://gitlab.inria.fr/why3/why3/-/archive/${version}/why3-${version}.tar.gz";
    hash = sha256;
  };

  nativeBuildInputs = [
    autoreconfHook
    dune
    ocaml
    wrapGAppsHook3
  ]
  ++ (with ocamlPackages; [
    findlib
    menhir
  ]);

  buildInputs = with ocamlPackages; [
    lablgtk3-sourceview3
  ];

  propagatedBuildInputs = with ocamlPackages; [
    camlzip
    menhirLib
    ocamlgraph
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

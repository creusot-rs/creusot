{
  # Dependencies
  creusot,
  darwin,
  ocamlPackages,
  zeromq,

  # Librairies
  fetchurl,
  lib,
  stdenv,

  # Pins
  sha256,
  version,
}:
ocamlPackages.buildDunePackage {
  inherit version;

  pname = "why3find";

  src = fetchurl {
    url = "https://github.com/creusot-rs/why3find/archive/${version}.tar.gz";
    hash = sha256;
  };

  nativeBuildInputs = lib.optionals stdenv.isDarwin [
    darwin.sigtool
  ];

  buildInputs = [
    creusot.why3
    zeromq
  ]
  ++ (with ocamlPackages; [
    dune-site
    terminal_size
    yojson
    zmq
  ]);
}

{
  # Dependencies
  creusot,
  darwin,
  ocamlPackages,
  zeromq,

  # Librairies
  fetchFromGitHub,
  lib,
  stdenv,

  # Pins
  sha256,
  version,
}:
ocamlPackages.buildDunePackage {
  inherit version;

  pname = "why3find";

  src = fetchFromGitHub {
    owner = "mcoulmance";
    repo = "why3find";
    rev = "c9ec1d03bdc92ab4ce991028613b70c5acc7022b";
    hash = "sha256-9xL/YDq9c03DGRvWWi7Ii//6JQp7b9cKN83MkG9GNnM=";
  };

  nativeBuildInputs = lib.optionals stdenv.isDarwin [
    darwin.sigtool
  ];

  patchPhase = ''
    rm -rf tests
  '';

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

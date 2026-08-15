{
  # Dependencies
  ocamlPackages,
  why3Framework,
  zeromq,

  # Librairies
  fetchurl,

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

  buildInputs = [
    why3Framework.why3
    zeromq
  ]
  ++ (with ocamlPackages; [
    dune-site
    terminal_size
    yojson
    zmq
  ]);
}

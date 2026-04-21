{
  pkgs,
  version,
  sha256,
  why3,
}:
with pkgs;
with ocamlPackages;
  buildDunePackage {
    inherit version;

    pname = "why3find";

    src = pkgs.fetchurl {
      url = "https://github.com/creusot-rs/why3find/archive/${version}.tar.gz";
      hash = sha256;
    };

    buildInputs = [
      dune-site
      terminal_size
      why3
      yojson
      zeromq
      zmq
    ];
  }

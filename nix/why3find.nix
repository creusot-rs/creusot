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
      url = "https://git.frama-c.com/pub/why3find/-/archive/${version}/why3find-${version}.tar.gz";
      hash = sha256;
    };

    buildInputs = [
      dune-site
      dune_3
      terminal_size
      why3
      yojson
      zeromq
      zmq
    ];
  }

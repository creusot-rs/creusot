{
  pkgs,
  version,
  sha256,
  why3,
}:
pkgs.ocamlPackages.buildDunePackage {
  inherit version;

  pname = "why3find";

  src = pkgs.fetchurl {
    url = "https://git.frama-c.com/pub/why3find/-/archive/${version}/why3find-${version}.tar.gz";
    hash = sha256;
  };

  buildInputs =
    [why3]
    ++ (with pkgs; [dune_3 zeromq])
    ++ (with pkgs.ocamlPackages; [
      dune-site
      terminal_size
      yojson
      zmq
    ]);
}

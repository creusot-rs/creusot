{
  pkgs,
  version,
  sha256,
}:
pkgs.why3.overrideAttrs {
  inherit version;

  src = pkgs.fetchurl {
    url = "https://why3.gitlabpages.inria.fr/releases/why3-${version}.tar.gz";
    hash = sha256;
  };
}

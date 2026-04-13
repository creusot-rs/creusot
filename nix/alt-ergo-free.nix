{
  pkgs,
  version,
  sha256,
}:
pkgs.alt-ergo-free.overrideAttrs {
  inherit version;

  src = pkgs.fetchurl {
    url = "https://github.com/OCamlPro/alt-ergo/releases/download/v${version}-free/alt-ergo-${version}-free.tar.gz";
    hash = sha256;
  };
}

{
  pkgs,
  version,
  sha256,
}:
pkgs.alt-ergo.overrideAttrs {
  inherit version;

  src = pkgs.fetchurl {
    url = "https://github.com/OCamlPro/alt-ergo/releases/download/v${version}/alt-ergo-${version}.tbz";
    hash = sha256;
  };
}

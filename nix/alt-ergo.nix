{
  # Previous overlay
  alt-ergo,

  # Librairies
  fetchurl,

  # Pins
  sha256,
  version,
}:
alt-ergo.overrideAttrs {
  inherit version;

  src = fetchurl {
    url = "https://github.com/OCamlPro/alt-ergo/releases/download/v${version}/alt-ergo-${version}.tbz";
    hash = sha256;
  };
}

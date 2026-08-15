{
  # Previous overlay
  alt-ergo-free,

  # Librairies
  fetchurl,

  # Pins
  sha256,
  version,
}:

alt-ergo-free.overrideAttrs {
  inherit version;

  src = fetchurl {
    url = "https://github.com/OCamlPro/alt-ergo/releases/download/v${version}-free/alt-ergo-${version}-free.tar.gz";
    hash = sha256;
  };
}

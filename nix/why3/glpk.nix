{
  # Dependencies
  autoreconfHook,

  # Previous overlay
  glpk,

  # Librairies
  fetchpatch,
  fetchurl,
  stdenv,
}:

stdenv.mkDerivation rec {
  inherit (glpk) meta;

  name = "glpk";
  version = "4.52";

  src = fetchurl {
    url = "mirror://gnu/glpk/${name}-${version}.tar.gz";
    sha256 = "sha256-ml2rNWJotPF3wz4A3fgWRJbcJDToO9ERQUcCTfmDo7s=";
  };

  patches = [
    (fetchpatch {
      name = "glpk-cut-log.patch";
      url = "https://raw.githubusercontent.com/cvc5/cvc5/99bfe0bcc00bf730c84db499b7e27419bf165dc3/cmake/deps-utils/glpk-cut-log.patch";
      sha256 = "sha256-/H9hwlFmiBk6Kh9C7G6UeA2xKJgZjfHNjHFQYXU10lM=";
    })
  ];

  preConfigure = ''
    sed -i '37d' src/minisat/minisat.h
  '';

  nativeBuildInputs = [ autoreconfHook ];
}

{
  # Dependencies
  bash,
  gmp,
  which,

  # Librairies
  fetchpatch,
  fetchurl,
  stdenv,
}:

stdenv.mkDerivation {
  name = "CoCoALib";

  src = fetchurl {
    url = "https://cocoa.altervista.org/cocoalib/tgz/CoCoALib-0.99800.tgz";
    sha256 = "sha256-+Lsifi4XKeFxz3rCAIr3HfJZFGB3EsNdt7y1oESpKMY=";
  };

  nativeBuildInputs = [ which ];
  buildInputs = [ gmp ];

  patches = [
    (fetchpatch {
      name = "CoCoALib-0.99800-trace.patch";
      url = "https://raw.githubusercontent.com/cvc5/cvc5/7de04e22fafc537d8c8f3188b32af64f3529e90c/cmake/deps-utils/CoCoALib-0.99800-trace.patch";
      sha256 = "sha256-IW+phNt+Ce01QaBiqnnxxy1ai4rSCckOyGO+Ymjwt+o=";
    })
  ];

  preConfigure = ''
    find . -type f -exec sed -i -e 's|/usr/bin/||g' {} \;
    find . -type f -exec sed -i -e 's|/bin/||g' {} \;
    find . -name "*.sh" -exec sed -i -e 's|bash|${bash}/bin/bash|g' {} \;
    sed -i -e '14s|.*|GMP_LIB="${gmp.dev}/lib/libgmp.so"|g' configuration/gmp-find-hdr.sh
    sed -i -e '106iexport LD_LIBRARY_PATH=${gmp}/lib' configuration/gmp-check-cxxflags.sh
    sed -i -e '1s|.*|exit 0|g' src/tests/RunTests.sh
    touch doc/CoCoALib.pdf examples/index.html
    mkdir $out $out/include $out/lib
  '';

  configureFlags = [
    "--with-libgmp=${gmp}/lib/libgmp.so"
  ];
}

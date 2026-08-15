{
  # Dependencies
  autoreconfHook,
  bash,
  cadical,
  cln,
  cmake,
  glpk,
  gmp,
  libedit,
  libpoly,
  pkg-config,
  python3,
  symfpu,
  which,

  # Previous overlay
  cvc5,

  # Librairies
  fetchFromGitHub,
  fetchpatch,
  fetchurl,
  stdenv,

  # Pins
  sha256,
  version,
}:
let
  cvc5-cadical = cadical.override { version = "2.1.3"; };

  cvc5-cocoalib = stdenv.mkDerivation {
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
  };

  cvc5-glpk = stdenv.mkDerivation rec {
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
  };

  cvc5-libpoly = libpoly.overrideAttrs {
    version = "0.2.0";
    src = fetchFromGitHub {
      owner = "SRI-CSL";
      repo = "libpoly";
      tag = "v0.2.0";
      hash = "sha256-gE2O1YfiVab/aIqheoMP8GhE+N3yho7kb5EP56pzjW8=";
    };
  };

  cvc5-symfpu = symfpu.overrideAttrs {
    version = "0-unstable-2019-05-17";
    src = fetchFromGitHub {
      owner = "martin-cs";
      repo = "symfpu";
      rev = "8fbe139bf0071cbe0758d2f6690a546c69ff0053";
      hash = "sha256-ONGfvJMo/HXlbxHmkFs9O5nhs6aDM+XuNSPgY+ykxck=";
    };
  };
in
stdenv.mkDerivation {
  inherit (cvc5) meta pname;
  inherit version;

  src = fetchFromGitHub {
    owner = "cvc5";
    repo = "cvc5";
    rev = "cvc5-${version}";
    hash = sha256;
  };

  nativeBuildInputs = [
    pkg-config
    cmake
  ];

  buildInputs = [
    cln
    cvc5-cadical
    cvc5-cocoalib
    cvc5-glpk
    cvc5-libpoly
    cvc5-symfpu
    gmp
    libedit
    python3.pkgs.pexpect
    python3.pkgs.pyparsing
  ];

  cmakeFlags = [
    "-DCMAKE_BUILD_TYPE=Production"
    "-DENABLE_GPL=1"

    "-DBUILD_SHARED_LIBS=1"
    "-DENABLE_ASAN=0"
    "-DENABLE_UBSAN=0"
    "-DENABLE_TSAN=0"
    "-DENABLE_ASSERTIONS=0"
    "-DENABLE_DEBUG_SYMBOLS=0"
    "-DENABLE_MUZZLE=0"
    "-DENABLE_SAFE_MODE=0"
    "-DENABLE_STABLE_MODE=0"
    "-DENABLE_STATISTICS=1"
    "-DENABLE_TRACING=0"
    "-DENABLE_UNIT_TESTING=0"
    "-DENABLE_VALGRIND=0"
    "-DENABLE_AUTO_DOWNLOAD=0"
    "-DUSE_PYTHON_VENV=0"
    "-DENABLE_IPO=0"

    "-DENABLE_COVERAGE=0"
    "-DENABLE_DEBUG_CONTEXT_MM=0"
    "-DENABLE_PROFILING=0"
    "-DTREAT_WARNING_AS_ERROR=0"

    "-DUSE_CLN=1"
    "-DUSE_COCOA=1"
    "-DUSE_CRYPTOMINISAT=0"
    "-DUSE_EDITLINE=0"
    "-DUSE_GLPK=1"
    "-DUSE_KISSAT=0"
    "-DUSE_POLY=1"

    "-DBUILD_BINDINGS_PYTHON=0"
    "-DBUILD_BINDINGS_JAVA=0"

    "-DBUILD_DOCS=0"
    "-DBUILD_DOCS_GA=0"

    "-DBUILD_GMP=0"
    "-DBUILD_CLN=0"

    "-DSKIP_COMPRESS_DEBUG=0"
    "-DSKIP_SET_RPATH=0"
    "-DUSE_DEFAULT_LINKER=1"
  ];
}

{
  pkgs,
  version,
  sha256,
}:
with pkgs; let
  cvc5-cadical = cadical.override {version = "2.1.3";};

  cvc5-cocoalib = stdenv.mkDerivation {
    name = "CoCoALib";

    src = fetchurl {
      url = "https://cocoa.altervista.org/cocoalib/tgz/CoCoALib-0.99800.tgz";
      sha256 = "sha256-+Lsifi4XKeFxz3rCAIr3HfJZFGB3EsNdt7y1oESpKMY=";
    };

    nativeBuildInputs = [which];
    buildInputs = [gmp];

    patches = [
      (fetchpatch {
        name = "CoCoALib-0.99800-trace.patch";
        url = "https://raw.githubusercontent.com/cvc5/cvc5/refs/heads/main/cmake/deps-utils/CoCoALib-0.99800-trace.patch";
        sha256 = "sha256-57Ptq3ESLGJjAT9xC8Uk0zrfMoRl+KsU6cg6QxIZH6k=";
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
        url = "https://raw.githubusercontent.com/cvc5/cvc5/refs/heads/main/cmake/deps-utils/glpk-cut-log.patch";
        sha256 = "sha256-/H9hwlFmiBk6Kh9C7G6UeA2xKJgZjfHNjHFQYXU10lM=";
      })
    ];

    nativeBuildInputs = [autoreconfHook];
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

    nativeBuildInputs = [pkg-config cmake];

    buildInputs = [
      cln
      cvc5-cadical
      cvc5-cocoalib
      cvc5-glpk
      gmp
      libedit
      libpoly
      python313Packages.pexpect
      python313Packages.pyparsing
      symfpu
    ];

    cmakeFlags = [
      "-DCMAKE_BUILD_TYPE=Production"
      "-DENABLE_GPL=1"

      "-DBUILD_SHARED_LIBS=1"
      "-DENABLE_ASAN=0"
      "-DENABLE_UBSAN=0"
      "-DENABLE_TSAN=0"
      "-DENABLE_ASSERTION=0"
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
      "-DUSE_EDITLINE=1"
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

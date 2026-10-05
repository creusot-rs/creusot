{
  # Dependencies
  autoreconfHook,
  bash,
  cadical,
  cln,
  cmake,
  gmp,
  libedit,
  libpoly,
  mpfr,
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

  cvc5-libpoly = libpoly.overrideAttrs {
    version = "0.2.1";
    src = fetchFromGitHub {
      owner = "SRI-CSL";
      repo = "libpoly";
      tag = "v0.2.1";
      hash = "sha256-uDWDio+RzJrgGKbWfT6S6voaJrJR0PzPfyr+33dr0ds=";
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
    cvc5-cadical
    cvc5-libpoly
    gmp
    libedit
    mpfr
    python3.pkgs.pexpect
    python3.pkgs.pyparsing
    symfpu
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

    "-DENABLE_CLANG_TIDY=0"
    "-DENABLE_COVERAGE=0"
    "-DENABLE_DEBUG_CONTEXT_MM=0"
    "-DENABLE_PROFILING=0"
    "-DTREAT_WARNING_AS_ERROR=0"
    "-DNO_GLOBAL_POLY_CTX=0"

    "-DUSE_CLN=0"
    "-DUSE_COCOA=0"
    "-DUSE_CRYPTOMINISAT=0"
    "-DUSE_EDITLINE=0"
    "-DUSE_GLPK=0"
    "-DUSE_KISSAT=0"
    "-DUSE_MPFR=1"
    "-DUSE_POLY=1"
    "-DUSE_NORMALIZ=0"

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

{
  # Dependencies
  autoreconfHook,
  cadical,
  cln,
  cmake,
  cocoalib,
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
    cadical
    cocoalib
    cln
    glpk
    gmp
    libedit
    libpoly
    python3
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

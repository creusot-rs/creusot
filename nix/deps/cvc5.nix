{
  # Dependencies
  buildPackages,
  pkgs,

  # Previous overlay
  cvc5,

  # Librairies
  fetchFromGitHub,
  lib,
  stdenv,

  # Pins
  sha256,
  version,
}:

let
  cadical = pkgs.cadical.override { version = "2.1.3"; };

  libpoly = pkgs.libpoly.overrideAttrs (old: {
    version = "0.2.1";
    src = fetchFromGitHub {
      owner = "SRI-CSL";
      repo = "libpoly";
      tag = "v0.2.1";
      hash = "sha256-uDWDio+RzJrgGKbWfT6S6voaJrJR0PzPfyr+33dr0ds=";
    };

    cmakeFlags = [
      "-DLIBPOLY_BUILD_PYTHON_API=0"
      "-DLIBPOLY_BUILD_STATIC=${if stdenv.hostPlatform.isStatic then "0" else "1"}"
    ];

    postPatch = lib.optionalString stdenv.hostPlatform.isStatic ''
      sed -i '77,105d' src/CMakeLists.txt
    '';
  });
in
stdenv.mkDerivation (
  {
    inherit (cvc5) meta pname;
    inherit version;

    src = fetchFromGitHub {
      owner = "cvc5";
      repo = "cvc5";
      rev = "cvc5-${version}";
      hash = sha256;
    };

    nativeBuildInputs = with buildPackages; [
      cmake
      (python3.withPackages (ps: [
        ps.pyexpect
        ps.pyparsing
      ]))
      pkg-config
    ];

    buildInputs = with pkgs; [
      cadical
      gmp
      libedit
      libpoly
      mpfr
      symfpu
    ];

    cmakeFlags = [
      "-DCMAKE_BUILD_TYPE=Production"
      "-DENABLE_GPL=1"

      "-DBUILD_SHARED_LIBS=${if stdenv.hostPlatform.isStatic then "0" else "1"}"

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

    installPhase = ''
      install -Dm755 bin/cvc5 $out/bin/cvc5
    '';

    postFixup = lib.optional stdenv.hostPlatform.isStatic ''
      rm -rf $out/nix-support
    '';
  }
  // lib.optionalAttrs stdenv.hostPlatform.isStatic {
    allowedReferences = [ "out" ];
    allowedRequisites = [ "out" ];
  }
)

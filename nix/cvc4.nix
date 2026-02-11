{
  version,
  sha256,
}:
_: pkgs:
{
  cvc4 = (pkgs.makeStatic pkgs.stdenv).mkDerivation {
    inherit (pkgs.cvc4) meta patches pname preConfigure;
    inherit version;

    src = pkgs.fetchFromGitHub {
      owner = "cvc5";
      repo = "cvc5";
      rev = "cvc4-${version}";
      hash = sha256;
    };

    nativeBuildInputs = with pkgs; [
      cmake
      pkg-config
      antlr3_4
      jdk
      python3
      python3.pkgs.toml
    ];

    buildInputs = with pkgs.pkgsStatic; [
      cadical
      cln
      cryptominisat
      libantlr3c
      symfpu
    ];

    outputs = ["out" "dev" "man"];

    cmakeFlags = [
      "-DCMAKE_BUILD_TYPE=Production"
      "-DCMAKE_POLICY_VERSION_MINIMUM=3.5"
      "-DENABLE_GPL=1"

      "-DENABLE_ASAN=0"
      "-DENABLE_UBSAN=0"
      "-DENABLE_TSAN=0"
      "-DENABLE_ASSERTIONS=0"
      "-DENABLE_COMP_INC_TRACK=0"
      "-DENABLE_DEBUG_SYMBOLS=0"
      "-DENABLE_DUMPING=0"
      "-DENABLE_MUZZLE=0"
      "-DENABLE_PROOFS=0"
      "-DENABLE_STATISTICS=1"
      "-DENABLE_TRACING=0"
      "-DENABLE_UNIT_TESTING=0"
      "-DENABLE_VALGRIND=0"
      "-DENABLE_SHARED=0"
      "-DENABLE_STATIC_BINARY=1"

      "-DENABLE_BEST=0"
      "-DENABLE_COVERAGE=0"
      "-DENABLE_DEBUG_CONTEXT_MM=0"
      "-DENABLE_PROFILING=0"

      "-DUSE_ABC=0"
      "-DUSE_CADICAL=1"
      "-DUSE_CLN=1"
      "-DUSE_CRYPTOMINISAT=1"
      "-DUSE_GLPK=0"
      "-DUSE_KISSAT=0"
      "-DUSE_READLINE=0"

      "-DUSE_DRAT2ER=0"
      "-DUSE_LFSC=0"
      "-DUSE_SYMFPU=1"
      "-DUSE_PYTHON2=0"
      "-DUSE_PYTHON3=1"

      "-DBUILD_SWIG_BINDINGS_JAVA=0"
      "-DBUILD_SWIG_BINDINGS_PYTHON=0"
      "-DBUILD_BINDINGS_PYTHON=0"
    ];
  };
}

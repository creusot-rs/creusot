{
  # Dependencies
  buildPackages,
  pkgs,

  # Previous overlay
  cvc4,

  # Librairies
  fetchFromGitHub,
  lib,
  stdenv,

  # Pins
  sha256,
  version,
}:

let
  cadical = pkgs.cadical.overrideAttrs { doCheck = false; };

  cln = (pkgs.cln.override { gccStdenv = stdenv; }).overrideAttrs (
    old:
    lib.optionalAttrs stdenv.hostPlatform.isStatic {
      NIX_CFLAGS_COMPILE = "${old.NIX_CFLAGS_COMPILE or ""} -DHZ=1000";
    }
  );

  cryptominisat = pkgs.cryptominisat.overrideAttrs {
    version = "5.8.0";
    src = fetchFromGitHub {
      owner = "msoos";
      repo = "cryptominisat";
      rev = "5.8.0";
      hash = "sha256-oGDsEYU9yXmHfbK4LyFzuJdfKHiFbSrT5PdY6GnrFQI=";
    };

    cmakeFlags = [
      "-DCMAKE_POLICY_VERSION_MINIMUM=3.5"

      "-DBUILD_SHARED_LIBS=${if stdenv.hostPlatform.isStatic then "0" else "1"}"

      "-DENABLE_PYTHON_INTERFACE=0"
      "-DONLY_SIMPLE=1"
    ];

    postPatch = ''
      sed -i -e '28i#include <cstdint>' src/ccnr.h

      substituteInPlace src/GitSHA1.cpp.in \
        --replace-fail '@CMAKE_CXX_COMPILER@' 'CXX' \
        --replace-fail '@PYTHON_EXECUTABLE@' 'python3'
    '';
  };

  symfpu = pkgs.symfpu.overrideAttrs {
    version = "0-unstable-2019-05-17";
    src = fetchFromGitHub {
      owner = "martin-cs";
      repo = "symfpu";
      rev = "8fbe139bf0071cbe0758d2f6690a546c69ff0053";
      hash = "sha256-ONGfvJMo/HXlbxHmkFs9O5nhs6aDM+XuNSPgY+ykxck=";
    };
  };
in
stdenv.mkDerivation (
  {
    inherit (cvc4) meta patches pname;
    inherit (cvc4) preConfigure;
    inherit version;

    src = fetchFromGitHub {
      owner = "cvc5";
      repo = "cvc5";
      rev = "cvc4-${version}";
      hash = sha256;
    };

    nativeBuildInputs = with buildPackages; [
      antlr3_4
      cmake
      jdk
      pkg-config
      (python3.withPackages (ps: [ ps.toml ]))
    ];

    buildInputs = with pkgs; [
      cadical
      cln
      cryptominisat
      gmp
      libantlr3c
      symfpu
    ];

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
      "-DENABLE_STATIC_BINARY=${if stdenv.hostPlatform.isStatic then "1" else "0"}"

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
      "-DUSE_PYTHON3=0"

      "-DBUILD_SWIG_BINDINGS_JAVA=0"
      "-DBUILD_SWIG_BINDINGS_PYTHON=0"
      "-DBUILD_BINDINGS_PYTHON=0"
    ];

    postPatch =
      (cvc4.postPatch or "")
      + ''
        sed -i '/#include <fpu_control.h>/d' \
          src/prop/minisat/utils/System.h \
          src/prop/bvminisat/utils/System.h
      ''
      + lib.optionalString stdenv.hostPlatform.isDarwin ''
        substituteInPlace src/main/CMakeLists.txt \
          --replace-fail 'if(ENABLE_STATIC_BINARY)' 'if(ENABLE_STATIC_BINARY AND NOT APPLE)'
      '';

    installPhase = ''
      install -Dm755 bin/cvc4 $out/bin/cvc4
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

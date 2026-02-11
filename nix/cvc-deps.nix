_: pkgs: {
  cadical = (pkgs.pkgsStatic.cadical.override {
    version = "2.1.3";
  }).overrideAttrs {
    prePatch = ''
      sed -i -e '104d' test/api/run.sh
    '';
  };

  cln = pkgs.pkgsStatic.cln.overrideAttrs {
    NIX_CFLAGS_COMPILE = "-DHZ=100";
  };

  cocoalib = (pkgs.makeStatic pkgs.stdenv).mkDerivation {
    name = "CoCoALib";

    src = pkgs.fetchurl {
      url = "https://cocoa.altervista.org/cocoalib/tgz/CoCoALib-0.99800.tgz";
      sha256 = "sha256-+Lsifi4XKeFxz3rCAIr3HfJZFGB3EsNdt7y1oESpKMY=";
    };

    nativeBuildInputs = with pkgs; [bintools which];
    buildInputs = [pkgs.pkgsStatic.gmp];

    patches = [
      (pkgs.fetchpatch {
        name = "CoCoALib-0.99800-trace.patch";
        url = "https://raw.githubusercontent.com/cvc5/cvc5/refs/heads/main/cmake/deps-utils/CoCoALib-0.99800-trace.patch";
        sha256 = "sha256-57Ptq3ESLGJjAT9xC8Uk0zrfMoRl+KsU6cg6QxIZH6k=";
      })
    ];

    preConfigure = ''
      find . -type f -exec sed -i -e 's|/usr/bin/||g' {} \;
      find . -type f -exec sed -i -e 's|/bin/||g' {} \;
      find . -name "*.sh" -exec sed -i -e 's|bash|${pkgs.bash}/bin/bash|g' {} \;
      sed -i -e '14s|.*|GMP_LIB="${pkgs.pkgsStatic.gmp.dev}/lib/libgmp.a"|g' configuration/gmp-find-hdr.sh
      sed -i -e '106iexport LD_LIBRARY_PATH=${pkgs.pkgsStatic.gmp}/lib' configuration/gmp-check-cxxflags.sh
      sed -i -e '1s|.*|exit 0|g' src/tests/RunTests.sh
      sed -i -e '111s|.*|all: check cocoa5-check examples server|g' Makefile
      mkdir $out $out/include $out/lib
    '';

    configurePlatforms = [];
    configureFlags = [
      "--no-boost"
      "--with-libgmp=${pkgs.pkgsStatic.gmp}/lib/libgmp.a"
    ];

    dontAddStaticConfigureFlags = true;
  };

  cryptominisat = pkgs.pkgsStatic.cryptominisat.overrideAttrs {
    src = pkgs.fetchFromGitHub {
      owner = "msoos";
      repo = "cryptominisat";
      rev = "5.8.0";
      hash = "sha256-oGDsEYU9yXmHfbK4LyFzuJdfKHiFbSrT5PdY6GnrFQI=";
    };

    cmakeFlags = [
      "-DCMAKE_POLICY_VERSION_MINIMUM=3.5"
      "-DENABLE_PYTHON_INTERFACE=0"

      "-DBUILD_SHARED_LIBS=0"
      "-DSTATICCOMPILE=1"
    ];

    patchPhase = ''
      sed -i -e '31,36d' src/main_exe.cpp
      sed -i -e '28i#include <cstdint>' src/ccnr.h
    '';
  };

  glpk = (pkgs.makeStatic pkgs.stdenv).mkDerivation rec {
    inherit (pkgs.glpk) meta;

    name = "glpk";
    version = "4.52";

    src = pkgs.fetchurl {
      url = "mirror://gnu/glpk/${name}-${version}.tar.gz";
      sha256 = "sha256-ml2rNWJotPF3wz4A3fgWRJbcJDToO9ERQUcCTfmDo7s=";
    };

    patches = [
      (pkgs.fetchpatch {
        name = "glpk-cut-log.patch";
        url = "https://raw.githubusercontent.com/cvc5/cvc5/refs/heads/main/cmake/deps-utils/glpk-cut-log.patch";
        sha256 = "sha256-/H9hwlFmiBk6Kh9C7G6UeA2xKJgZjfHNjHFQYXU10lM=";
      })
    ];

    nativeBuildInputs = [pkgs.autoreconfHook];
  };

  libpoly = pkgs.pkgsStatic.libpoly.overrideAttrs {
    patchPhase = ''
      sed -i -e '77,106d' src/CMakeLists.txt
    '';

    cmakeFlags = [
      "-DLIBPOLY_BUILD_PYTHON_API=0"
    ];
  };
}

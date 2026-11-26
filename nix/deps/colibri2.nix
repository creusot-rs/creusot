{
  # Dependencies
  flint,
  gmp,
  m4,
  mpfr,
  ocamlPackages,
  pkg-config,

  # Librairies
  fetchurl,
  lib,
  stdenv,

  # Pins
  sha256,
  version,
}:

let
  pname = "colibri2";

  src = fetchurl {
    url = "https://git.frama-c.com/pub/colibrics/-/archive/${version}/colibrics-${version}.tar.gz";
    hash = sha256;
  };
in

let
  # NOTE: Colibri2 needs more recent versions of the following libraries than nixpkgs provides.
  patricia-tree = ocamlPackages.patricia-tree.overrideAttrs {
    version = "0.15.0";
    src = fetchurl {
      url = "https://github.com/codex-semantics-library/patricia-tree/releases/download/v0.15.0/patricia-tree-0.15.0.tbz";
      hash = "sha256-4P5mq32lsq0kC2RDDWBfQGS8cEv0h6zGMU/YaOmOwnk=";
    };
    doCheck = false;
  };

  trace = ocamlPackages.trace.overrideAttrs {
    version = "0.12";
    src = fetchurl {
      url = "https://github.com/ocaml-tracing/ocaml-trace/releases/download/v0.12/trace-0.12.tbz";
      hash = "sha256-wXPWv5Qz6e60G73doRailjc9RYZYQdy7eL/zvoq9n9g=";
    };
  };

  trace-tef = ocamlPackages.trace-tef.overrideAttrs {
    inherit (trace) version src;
    propagatedBuildInputs = [
      trace
      ocamlPackages.mtime
    ];
    # The nixpkgs patch removing the `atomic` dependency no longer applies.
    postPatch = "";
    doCheck = false;
  };

  # NOTE: The following libraries are not packaged in nixpkgs.

  # OCaml bindings to the FLINT library
  ocaml-flint = ocamlPackages.buildDunePackage {
    pname = "flint";
    version = "0.4.2";

    src = fetchurl {
      url = "https://github.com/bobot/ocaml-flint/releases/download/0.4.2/flint-0.4.2.tbz";
      hash = "sha256-hv4NtXjX4hFgUowH/9yAN15kk3HhxfvJ9Qqv2Zyh3bo=";
    };

    nativeBuildInputs = [ pkg-config ];
    buildInputs = [ ocamlPackages.dune-configurator ];
    propagatedBuildInputs = [
      flint
      gmp
      mpfr
    ]
    ++ (with ocamlPackages; [
      ctypes
      zarith
    ]);
  };

  # OCaml bindings to the CUDD library (provides the findlib package `cudd`)
  mlcuddidl = stdenv.mkDerivation {
    pname = "ocaml${ocamlPackages.ocaml.version}-mlcuddidl";
    version = "3.0.8";

    src = fetchurl {
      url = "https://framagit.org/nberth/mlcuddidl/-/archive/3.0.8/mlcuddidl-3.0.8.tar.gz";
      hash = "sha256-JrIrHx6tWhnqdCNIK1L1tcSYo9G54TzgVmIKd6VJir0=";
    };

    # Same patches as the opam package
    patches = [
      (fetchurl {
        url = "https://raw.githubusercontent.com/ocaml/opam-source-archives/main/patches/mlcuddidl/compilation_ocaml5.diff";
        hash = "sha256-3j/F+7gaakd9bCsp4TPDIo37VyvR2ZUNhN/WFCIQBMU=";
      })
      (fetchurl {
        url = "https://raw.githubusercontent.com/ocaml/opam-source-archives/main/patches/mlcuddidl/exn_init_val_unit.diff";
        hash = "sha256-oAzqrKCqJrH6vRzbiTdp9d5sVIH/MzMQNcb7+RIQsMc=";
      })
    ];

    strictDeps = true;

    nativeBuildInputs = [
      m4
    ]
    ++ (with ocamlPackages; [
      camlidl
      findlib
      ocaml
    ]);

    # `cudd.cmxa` links against `libcamlidl.a`.
    propagatedBuildInputs = [ ocamlPackages.camlidl ];

    # The configure script is hand-written: it does not understand `--prefix=`.
    dontAddPrefix = true;
    configureFlags = [ "--disable-profiling" ];

    createFindlibDestdir = true;
    postConfigure = ''
      mkdir -p $OCAMLFIND_DESTDIR/stublibs
    '';
  };

  colibrilib = ocamlPackages.buildDunePackage {
    inherit version src;
    pname = "colibrilib";

    propagatedBuildInputs = [ ocamlPackages.zarith ];
  };
in

ocamlPackages.buildDunePackage {
  inherit pname version src;

  buildInputs = [
    colibrilib
    mlcuddidl
    ocaml-flint
    patricia-tree
    trace
    trace-tef
  ]
  ++ (with ocamlPackages; [
    base
    cmdliner
    containers
    dolmen
    dolmen_loop
    dolmen_type
    dune-build-info
    farith
    gen
    gmap
    ocamlgraph
    ocplib-simplex
    ppx_deriving
    ppx_hash
    ppx_here
    ppx_inline_test
    ppx_optcomp
    qcheck-core
    re
    zarith
  ]);

  meta = {
    description = "CP solver for SMT-LIB";
    homepage = "https://colibri.frama-c.com";
    license = lib.licenses.lgpl21Only;
    mainProgram = "colibri2";
  };
}

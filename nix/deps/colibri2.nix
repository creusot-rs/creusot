{
  # Dependencies
  darwin,
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

# NOTE: Update this when NixOS 26.11 is released
let
  dolmen = ocamlPackages.dolmen.overrideAttrs (old: {
    version = "0.11";
    src = fetchurl {
      url = "https://github.com/Gbury/dolmen/releases/download/v0.11/dolmen-0.11.tbz";
      hash = "sha256-I1x4ofTavGwRbT0c9Rryhss/vtcTxhFs1dGxy+0MyH8=";
    };

    nativeBuildInputs = old.nativeBuildInputs ++ lib.optionals stdenv.isDarwin [
      darwin.sigtool
    ];

    propagatedBuildInputs =
      old.propagatedBuildInputs
      ++ (with ocamlPackages; [
        dune-site
        seq
        uutf
      ]);
  });

  dolmen_type = ocamlPackages.dolmen_type.override { inherit dolmen; };

  dolmen_loop = (ocamlPackages.dolmen_loop.override { inherit dolmen dolmen_type; }).overrideAttrs (old: {
    propagatedBuildInputs = old.propagatedBuildInputs ++ [ ocamlPackages.zarith ];
    doCheck = false;
  });

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

    postPatch = "";
    doCheck = false;
  };

  # Generator of C stubs, used to build `ocaml-flint`
  camlid = ocamlPackages.buildDunePackage {
    pname = "camlid";
    version = "0.3";

    src = fetchurl {
      url = "https://github.com/bobot/camlid/releases/download/0.3/camlid-0.3.tbz";
      hash = "sha256-CGZVIDbEUqHN0Fc4p2ESt2HbbM7u7SsfWgPXMKGSScA=";
    };

    propagatedBuildInputs = [ ocamlPackages.fmt ];
  };

  ocaml-flint = ocamlPackages.buildDunePackage {
    pname = "flint";
    version = "0.5.0";

    src = fetchurl {
      url = "https://github.com/bobot/ocaml-flint/releases/download/0.5.0/flint-0.5.0.tbz";
      hash = "sha256-ccP2rhsdI/FAsKVQnHmJ4z2m9N70X2T21x7LQbgdtzE=";
    };

    dontConfigure = true;

    buildInputs = [
      camlid
      ocamlPackages.dune-configurator
    ];
    propagatedBuildInputs = [
      flint
      ocamlPackages.zarith
    ];
  };

  mlcuddidl = stdenv.mkDerivation {
    pname = "mlcuddidl";
    version = "3.0.8";

    src = fetchurl {
      url = "https://framagit.org/nberth/mlcuddidl/-/archive/3.0.8/mlcuddidl-3.0.8.tar.gz";
      hash = "sha256-JrIrHx6tWhnqdCNIK1L1tcSYo9G54TzgVmIKd6VJir0=";
    };

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

    propagatedBuildInputs = [ ocamlPackages.camlidl ];

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

    propagatedBuildInputs = [
      ocaml-flint
      ocamlPackages.zarith
    ];
  };
in

ocamlPackages.buildDunePackage {
  inherit pname version src;

  nativeBuildInputs = lib.optionals stdenv.isDarwin [
    darwin.sigtool
  ];

  buildInputs = [
    colibrilib
    dolmen
    dolmen_loop
    dolmen_type
    mlcuddidl
    ocaml-flint
    patricia-tree
    trace
    trace-tef
  ]
  ++ (with ocamlPackages; [
    cmdliner
    containers
    dune-build-info
    farith
    gmap
    ocamlgraph
    ocplib-simplex
    ppx_hash
    ppx_here
    ppx_inline_test
    qcheck-core
    re
  ]);

  meta = {
    description = "CP solver for SMT-LIB";
    homepage = "https://colibri.frama-c.com";
    license = lib.licenses.lgpl21Only;
    mainProgram = "colibri2";
  };
}

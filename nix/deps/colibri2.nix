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
  # The C library, shadowed below by its OCaml bindings of the same name.
  libflint = flint;

  # Colibri2 needs more recent versions of some OCaml libraries than nixpkgs
  # provides, and a few that nixpkgs does not package at all. The versions
  # are the ones opam picks for `colibri2.opam`.
  colibriPackages = ocamlPackages.overrideScope (
    self: super: {
      patricia-tree = super.patricia-tree.overrideAttrs {
        version = "0.15.0";
        src = fetchurl {
          url = "https://github.com/codex-semantics-library/patricia-tree/releases/download/v0.15.0/patricia-tree-0.15.0.tbz";
          hash = "sha256-4P5mq32lsq0kC2RDDWBfQGS8cEv0h6zGMU/YaOmOwnk=";
        };
        doCheck = false;
      };

      # `trace-tef` inherits its `src` and `version` from `trace`.
      trace = super.trace.overrideAttrs {
        version = "0.12";
        src = fetchurl {
          url = "https://github.com/ocaml-tracing/ocaml-trace/releases/download/v0.12/trace-0.12.tbz";
          hash = "sha256-wXPWv5Qz6e60G73doRailjc9RYZYQdy7eL/zvoq9n9g=";
        };
      };

      trace-tef = super.trace-tef.overrideAttrs {
        # The nixpkgs patch removing the `atomic` dependency no longer applies.
        postPatch = "";
        doCheck = false;
      };

      # OCaml bindings to the FLINT library
      flint = self.buildDunePackage {
        pname = "flint";
        version = "0.4.2";

        src = fetchurl {
          url = "https://github.com/bobot/ocaml-flint/releases/download/0.4.2/flint-0.4.2.tbz";
          hash = "sha256-hv4NtXjX4hFgUowH/9yAN15kk3HhxfvJ9Qqv2Zyh3bo=";
        };

        nativeBuildInputs = [ pkg-config ];

        buildInputs = [ self.dune-configurator ];

        propagatedBuildInputs = [
          gmp
          libflint
          mpfr
          self.ctypes
          self.zarith
        ];
      };

      # OCaml bindings to the CUDD library (provides the findlib package `cudd`)
      mlcuddidl = stdenv.mkDerivation {
        pname = "ocaml${self.ocaml.version}-mlcuddidl";
        version = "3.0.8";

        src = fetchurl {
          url = "https://framagit.org/nberth/mlcuddidl/-/archive/3.0.8/mlcuddidl-3.0.8.tar.gz";
          hash = "sha256-JrIrHx6tWhnqdCNIK1L1tcSYo9G54TzgVmIKd6VJir0=";
        };

        # Same patches as the opam package
        patches =
          lib.optionals (lib.versionAtLeast self.ocaml.version "5") [
            (fetchurl {
              url = "https://raw.githubusercontent.com/ocaml/opam-source-archives/main/patches/mlcuddidl/compilation_ocaml5.diff";
              hash = "sha256-3j/F+7gaakd9bCsp4TPDIo37VyvR2ZUNhN/WFCIQBMU=";
            })
          ]
          ++ [
            (fetchurl {
              url = "https://raw.githubusercontent.com/ocaml/opam-source-archives/main/patches/mlcuddidl/exn_init_val_unit.diff";
              hash = "sha256-oAzqrKCqJrH6vRzbiTdp9d5sVIH/MzMQNcb7+RIQsMc=";
            })
          ];

        strictDeps = true;

        nativeBuildInputs = [
          m4
          self.camlidl
          self.findlib
          self.ocaml
        ];

        # `cudd.cmxa` links against `libcamlidl.a`.
        propagatedBuildInputs = [ self.camlidl ];

        # The configure script is hand-written: it does not understand `--prefix=`.
        dontAddPrefix = true;
        configureFlags = [ "--disable-profiling" ];

        createFindlibDestdir = true;
        postConfigure = ''
          mkdir -p $OCAMLFIND_DESTDIR/stublibs
        '';
      };

      colibrilib = self.buildDunePackage {
        pname = "colibrilib";
        inherit version;

        src = fetchurl {
          url = "https://git.frama-c.com/api/v4/projects/879/packages/generic/colibri2/${version}/colibri2-${version}.tbz";
          hash = sha256;
        };

        propagatedBuildInputs = [ self.zarith ];
      };

      colibri2 = self.buildDunePackage {
        pname = "colibri2";
        inherit version;
        inherit (self.colibrilib) src;

        buildInputs = with self; [
          base
          cmdliner
          colibrilib
          containers
          dolmen
          dolmen_loop
          dolmen_type
          dune-build-info
          farith
          flint
          gen
          gmap
          mlcuddidl
          ocamlgraph
          ocplib-simplex
          patricia-tree
          ppx_deriving
          ppx_hash
          ppx_here
          ppx_inline_test
          ppx_optcomp
          qcheck-core
          re
          trace
          trace-tef
          zarith
        ];

        meta = {
          description = "CP solver for SMT-LIB";
          homepage = "https://colibri.frama-c.com";
          license = lib.licenses.lgpl21Only;
          mainProgram = "colibri2";
        };
      };
    }
  );
in
colibriPackages.colibri2

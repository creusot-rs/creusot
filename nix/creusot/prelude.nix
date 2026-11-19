{
  # Dependencies
  libiconv,
  libzip,

  # Librairies
  formats,
  lib,
  runCommand,
  stdenv,

  # Attributes
  meta,
  rustBuilder,
  version,
}:
let
  pname = "prelude-generator";
  cargoExtraArgs = "--bin prelude-generator";

  src = lib.fileset.toSource {
    root = ../..;
    fileset = lib.fileset.unions [
      ../../Cargo.lock
      ../../prelude-generator
    ];
  };

  cargoToml =
    let
      manifest = builtins.fromTOML (builtins.readFile ../../Cargo.toml);
    in
    (formats.toml { }).generate "Cargo.toml" (
      manifest
      // {
        workspace = manifest.workspace // {
          members = [ "prelude-generator" ];
        };
      }
    );

  postUnpack = ''
    cp ${cargoToml} "$sourceRoot/Cargo.toml"
  '';

  preludeBinary = rustBuilder.buildPackage {
    inherit meta pname version;
    inherit cargoExtraArgs src;
    inherit postUnpack;

    cargoArtifacts = rustBuilder.buildDepsOnly {
      inherit meta pname version;
      inherit cargoExtraArgs src;
      inherit postUnpack;
    };

    nativeBuildInputs = lib.optionals stdenv.isDarwin [
      libiconv
      libzip
    ];
  };
in
runCommand "prelude"
  {
    nativeBuildInputs = [ preludeBinary ];
  }
  ''
    mkdir -p $out/share/why3find ./prelude-generator ./target/creusot
    cp ${src}/prelude-generator/*.coma ./prelude-generator

    CARGO_MANIFEST_DIR=./target ${preludeBinary}/bin/prelude-generator

    cp -r ./target/creusot/packages $out/share/why3find/.
  ''

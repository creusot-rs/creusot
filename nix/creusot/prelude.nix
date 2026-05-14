{
  # Dependencies
  libiconv,
  libzip,

  # Librairies
  lib,
  runCommand,
  stdenv,

  # Attributes
  meta,
  rustBuilder,
  src,
  version,
}:
let
  pname = "prelude-generator";
  cargoExtraArgs = "--bin prelude-generator";

  cargoArtifacts = rustBuilder.buildDepsOnly {
    inherit meta pname version;
    inherit cargoExtraArgs src;
  };

  preludeBinary = rustBuilder.buildPackage {
    inherit meta pname version;
    inherit cargoArtifacts cargoExtraArgs src;

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

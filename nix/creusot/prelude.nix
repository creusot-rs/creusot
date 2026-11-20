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
  postUnpack,
  version,
}:
let
  pname = "prelude-generator";
  cargoExtraArgs = "--bin prelude-generator";

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

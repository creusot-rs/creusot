{
  # Dependencies
  libiconv,
  libzip,

  # Librairies
  lib,
  runCommand,
  stdenv,

  # Attributes
  envBuilder,
  meta,
  src,
  version,
}:
let
  pname = "prelude-generator";
  cargoExtraArgs = "--bin prelude-generator";

  cargoArtifacts = envBuilder.buildDepsOnly {
    inherit meta version;
    inherit cargoExtraArgs pname src;
  };

  preludeBinary = envBuilder.buildPackage {
    inherit
      cargoArtifacts
      cargoExtraArgs
      meta
      pname
      src
      version
      ;

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

{
  # Dependencies
  libiconv,
  libzip,

  # Librairies
  lib,
  stdenv,

  # Attributes
  meta,
  rustBuilder,
  rustToolchain,
  src,
  version,
}:

let
  pname = "cargo-creusot";
  cargoExtraArgs = "--workspace --exclude creusot-install --exclude prelude-generator";

  cargoArtifacts = rustBuilder.buildDepsOnly {
    inherit meta pname version;
    inherit cargoExtraArgs src;
  };
in
rustBuilder.buildPackage rec {
  inherit meta pname version;
  inherit cargoArtifacts cargoExtraArgs src;

  nativeBuildInputs = lib.optionals stdenv.isDarwin [
    libiconv
    libzip
  ];

  doNotRemoveReferencesToRustToolchain = true;

  postInstall = ''
    mkdir $out/share
    cp {Cargo.toml,Cargo.lock} $out/share/.
    cp -r {creusot-std,creusot-std-proc,pearlite-syn} $out/share/.
  '';
}

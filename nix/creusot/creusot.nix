{
  # Dependencies
  libiconv,
  libzip,

  # Librairies
  lib,
  stdenv,

  # Attributes
  check,
  meta,
  rustBuilder,
  rustToolchain,
  src,
  postUnpack,
  version,
}:

let
  pname = "cargo-creusot";
  cargoExtraArgs = "--workspace";

  nativeBuildInputs = lib.optionals stdenv.isDarwin [
    libiconv
    libzip
  ];
in
rustBuilder.buildPackage rec {
  inherit meta pname version;
  inherit cargoExtraArgs nativeBuildInputs;
  inherit src postUnpack;

  cargoArtifacts = rustBuilder.buildDepsOnly {
    inherit meta pname version;
    inherit cargoExtraArgs src;
    inherit postUnpack;
  };

  doCheck = false;
  doNotRemoveReferencesToRustToolchain = true;

  passthru = {
    inherit (check) src postUnpack;
    inherit cargoArtifacts pname nativeBuildInputs;
  };

  postInstall = ''
    mkdir $out/share
    cp {Cargo.toml,Cargo.lock} $out/share/.
    cp -r {creusot-std,creusot-std-proc,pearlite-syn} $out/share/.
  '';
}

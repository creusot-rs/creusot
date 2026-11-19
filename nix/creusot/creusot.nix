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
  postUnpack,
  version,
}:

let
  pname = "cargo-creusot";
  cargoExtraArgs = "--workspace";

  manifest = builtins.fromTOML (builtins.readFile ../../Cargo.toml);

in
rustBuilder.buildPackage rec {
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

  doCheck = false;
  doNotRemoveReferencesToRustToolchain = true;

  postInstall = ''
    mkdir $out/share
    cp {Cargo.toml,Cargo.lock} $out/share/.
    cp -r {creusot-std,creusot-std-proc,pearlite-syn} $out/share/.
  '';
}

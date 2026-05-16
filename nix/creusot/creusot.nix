{
  # Dependencies
  libiconv,
  libzip,
  makeWrapper,

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

  nativeBuildInputs = [
    makeWrapper
  ]
  ++ lib.optionals stdenv.isDarwin [
    libiconv
    libzip
  ];

  doNotRemoveReferencesToRustToolchain = true;

  postInstall = ''
    mkdir $out/share
    cp {Cargo.toml,Cargo.lock} $out/share/.
    cp -r {creusot-std,creusot-std-proc,pearlite-syn} $out/share/.

    wrapProgram $out/bin/cargo-creusot \
      --set CREUSOT_PATH $out/share/ \
      --set CREUSOT_RUSTC $out/bin/creusot-rustc \

    wrapProgram $out/bin/creusot-rustc \
      --set LD_LIBRARY_PATH "${lib.makeLibraryPath [ rustToolchain ]}" \
      --set DYLD_FALLBACK_LIBRARY_PATH "${lib.makeLibraryPath [ rustToolchain ]}"
  '';
}

{
  # Dependencies
  libiconv,
  libzip,
  makeWrapper,

  # Librairies
  lib,
  stdenv,

  # Attributes
  envBuilder,
  meta,
  src,
  toolchain,
  version,
}:

let
  pname = "cargo-creusot";
  cargoExtraArgs = "--workspace --exclude creusot-install --exclude prelude-generator";
in
envBuilder.buildPackage rec {
  inherit
    cargoExtraArgs
    meta
    pname
    src
    version
    ;

  nativeBuildInputs = [
    makeWrapper
  ]
  ++ lib.optionals stdenv.isDarwin [
    libiconv
    libzip
  ];

  cargoArtifacts = envBuilder.buildDepsOnly {
    inherit
      cargoExtraArgs
      meta
      pname
      src
      version
      ;
  };

  doNotRemoveReferencesToRustToolchain = true;

  postInstall = with lib.strings; ''
    mkdir $out/share
    cp {Cargo.toml,Cargo.lock} $out/share/.
    cp -r {creusot-std,creusot-std-proc,pearlite-syn} $out/share/.

    wrapProgram $out/bin/cargo-creusot \
      --set CREUSOT_STD $out/share/creusot-std \
      --set CREUSOT_RUSTC $out/bin/creusot-rustc \

    wrapProgram $out/bin/creusot-rustc \
      --set LD_LIBRARY_PATH "${makeLibraryPath [ toolchain ]}" \
      --set DYLD_FALLBACK_LIBRARY_PATH "${makeLibraryPath [ toolchain ]}"
  '';
}

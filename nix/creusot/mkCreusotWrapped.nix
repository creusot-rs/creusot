{
  # Dependencies
  creusot,
  libiconv,
  rustToolchain,

  # Librairies
  buildEnv,
  lib,
  makeWrapper,
  stdenv,
  writeShellScriptBin,
}:

let
  components = rustToolchain.passthru.availableComponents;

  rustSysroot = stdenv.mkDerivation {
    name = "rust-sysroot";
    buildCommand = ''
      mkdir -p $out
      cp -rs --no-preserve=mode ${components.rustc}/libexec $out/
      cp -rs --no-preserve=mode ${components.rust-src}/lib $out/
      rm -f $out/lib/rustlib/src/rust/library/Cargo.lock
    '';
  };

  rustcWrapped = writeShellScriptBin "rustc" ''
    if [ "$1" = "--print" ] && [ "$2" = "sysroot" ]; then
      echo ${rustSysroot}
      exit 0
    fi
    exec "${rustToolchain}/bin/rustc" "$@"
  '';
in
# Arguments
{
  cargo ? components.cargo,
  isFree,
  rust-analyzer ? null,
}:

let
  why3Framework = creusot.mkWhy3Framework { inherit isFree; };
in
buildEnv {
  name = "creusot-wrapped";
  paths = [
    (lib.hiPrio cargo)
    creusot.prelude
    creusot.creusot
    why3Framework
  ]
  ++ lib.optional (rust-analyzer != null) (lib.hiPrio rust-analyzer)
  ++ lib.optional stdenv.isDarwin libiconv;

  nativeBuildInputs = [ makeWrapper ];
  postBuild = ''
    wrapProgram $out/bin/cargo \
      --add-flag "--config" \
      --add-flag "patch.crates-io.creusot-std.path=\"$out/share/creusot-std\"" \
      ${lib.optionalString stdenv.isDarwin ''--prefix LIBRARY_PATH : "${libiconv}/lib"''}

    wrapProgram $out/bin/cargo-creusot \
      --set CARGO "$out/bin/cargo" \
      --set CREUSOT_DATA_HOME "$out"
  ''
  + lib.optionalString (rust-analyzer != null) ''
    wrapProgram $out/bin/rust-analyzer \
      --prefix PATH : "${rustcWrapped}/bin"
  '';

  passthru = { inherit why3Framework; };
}

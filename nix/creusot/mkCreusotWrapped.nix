{
  # Dependencies
  bash,
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
in
# Arguments
{
  isFree,
  cargo ? components.cargo,
  rust-std ? components.rust-std,
  rust-src ? components.rust-src,
  rust-analyzer ? null,
  rust-analyzer-proc-macro-srv ? components.rustc,
}:

let
  why3Framework = creusot.mkWhy3Framework { inherit isFree; };

  rustSysroot = stdenv.mkDerivation {
    name = "rust-sysroot";
    buildCommand = ''
      mkdir -p $out
      cp -rs --no-preserve=mode ${rust-src}/lib $out/
      cp -rs --no-preserve=mode ${rust-std}/lib $out/
      cp -rs --no-preserve=mode ${rust-analyzer-proc-macro-srv}/libexec $out/
      rm -f $out/lib/rustlib/src/rust/library/Cargo.lock
    '';
  };

  rustcWrapped = writeShellScriptBin "rustc" ''
    for arg in "$@"; do
      case "$arg" in
        --sysroot | --sysroot=*)
          exec "${components.rustc}/bin/rustc" "$@"
          ;;
      esac
    done
    exec "${components.rustc}/bin/rustc" --sysroot "${rustSysroot}" "$@"
  '';

  creusotWrapped = writeShellScriptBin "creusot-rustc" ''
    for arg in "$@"; do
      case "$arg" in
        --sysroot | --sysroot=*)
          exec "${creusot.creusot}/bin/creusot-rustc" "$@"
          ;;
      esac
    done
    exec "${creusot.creusot}/bin/creusot-rustc" --sysroot "${rustSysroot}" "$@"
  '';

  cargoWrapped = writeShellScriptBin "cargo" ''
    for arg in "$@"; do
      if [[ "$arg" == "clippy" ]]; then
        exec "${cargo}/bin/cargo" "$@" "--config" "patch.crates-io.creusot-std.path=\"${creusot.creusot}/share/creusot-std\""
      fi
    done
    exec "${cargo}/bin/cargo" "--config" "patch.crates-io.creusot-std.path=\"${creusot.creusot}/share/creusot-std\"" "$@"
  '';
in
buildEnv {
  name = "creusot-wrapped";
  paths = [
    (lib.hiPrio cargoWrapped)
    (lib.hiPrio creusotWrapped)
    creusot.prelude
    creusot.creusot
    why3Framework
  ]
  ++ lib.optional (rust-analyzer != null) (lib.hiPrio rust-analyzer)
  ++ lib.optional stdenv.isDarwin libiconv;

  nativeBuildInputs = [ makeWrapper ];
  postBuild = ''
    wrapProgram $out/bin/cargo \
      ${lib.optionalString stdenv.isDarwin ''--prefix LIBRARY_PATH : "${libiconv}/lib"''}

    wrapProgram $out/bin/cargo-creusot \
      --set CARGO $out/bin/cargo \
      --set CREUSOT_DATA_HOME $out \
      --set CREUSOT_PATH $out/share/ \
      --set CREUSOT_RUSTC $out/bin/creusot-rustc

    wrapProgram $out/bin/creusot-rustc \
      --set LD_LIBRARY_PATH "${lib.makeLibraryPath [ rustToolchain ]}" \
      --set DYLD_FALLBACK_LIBRARY_PATH "${lib.makeLibraryPath [ rustToolchain ]}"
  ''
  + lib.optionalString (rust-analyzer != null) ''
    wrapProgram $out/bin/rust-analyzer \
      --prefix PATH : "${rustcWrapped}/bin" \
      --set RUST_SRC_PATH "${rustSysroot}/lib/rustlib/src/rust/library" \
      --set RUSTUP_AUTO_INSTALL 0
  '';

  passthru = { inherit why3Framework; };
}

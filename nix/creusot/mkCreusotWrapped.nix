{
  # Dependencies
  creusot,
  libiconv,
  makeWrapper,
  rustToolchain,

  # Librairies
  buildEnv,
  lib,
  stdenv,
}:

# Arguments
{
  cargo ? rustToolchain.passthru.availableComponents.cargo,
  isFree,
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
  '';

  passthru = { inherit why3Framework; };
}

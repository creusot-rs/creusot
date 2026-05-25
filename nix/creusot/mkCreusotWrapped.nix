{
  # Dependencies
  creusot,
  makeWrapper,
  rustToolchain,

  # Librairies
  buildEnv,
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
    cargo
    creusot.prelude
    creusot.creusot
    why3Framework
  ];

  nativeBuildInputs = [ makeWrapper ];
  postBuild = ''
    wrapProgram $out/bin/cargo \
      --add-flag "--config" \
      --add-flag "patch.crates-io.creusot-std.path=\"$out/share/creusot-std\""

    wrapProgram $out/bin/cargo-creusot \
      --set CARGO "$out/bin/cargo" \
      --set CREUSOT_DATA_HOME "$out"
  '';

  passthru = { inherit why3Framework; };
}

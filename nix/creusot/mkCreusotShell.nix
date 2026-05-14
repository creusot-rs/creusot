{
  # Dependencies
  creusot,
  gcc,
  makeWrapper,

  # Librairies
  buildEnv,

  # Attributes
  rustToolchain,
}:

# Arguments
{
  isFree,
}:

let
  why3Framework = creusot.mkWhy3Framework { inherit isFree; };
in
buildEnv {
  name = "creusot-env";
  paths = [
    creusot.prelude
    creusot.creusot
    gcc
    rustToolchain
    why3Framework
  ];

  nativeBuildInputs = [ makeWrapper ];
  postBuild = ''
    wrapProgram $out/bin/cargo-creusot \
      --set CREUSOT_DATA_HOME "$out"
  '';

  passthru = { inherit why3Framework; };
}

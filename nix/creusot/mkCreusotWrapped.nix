{
  # Dependencies
  creusot,
  gcc,
  makeWrapper,

  # Librairies
  buildEnv,
}:

# Arguments
{
  isFree,
}:

let
  why3Framework = creusot.mkWhy3Framework { inherit isFree; };
in
buildEnv {
  name = "creusot-wrapped";
  paths = [
    creusot.prelude
    creusot.creusot
    why3Framework
  ];

  nativeBuildInputs = [ makeWrapper ];
  postBuild = ''
    wrapProgram $out/bin/cargo-creusot \
      --set CREUSOT_DATA_HOME "$out"
  '';

  passthru = { inherit why3Framework; };
}

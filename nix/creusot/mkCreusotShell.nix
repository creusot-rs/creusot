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
buildEnv {
  name = "creusot-env";
  paths = [
    creusot.prelude
    creusot.creusot
    (creusot.mkWhy3Framework isFree)
    gcc
    rustToolchain
  ];

  nativeBuildInputs = [ makeWrapper ];
  postBuild = ''
    wrapProgram $out/bin/cargo-creusot \
      --set CREUSOT_DATA_HOME "$out"
  '';
}

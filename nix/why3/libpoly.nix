{
  # Previous overlay
  libpoly,

  # Librairies
  fetchFromGitHub,
}:

libpoly.overrideAttrs {
  version = "0.2.0";

  src = fetchFromGitHub {
    owner = "SRI-CSL";
    repo = "libpoly";
    tag = "v0.2.0";
    hash = "sha256-gE2O1YfiVab/aIqheoMP8GhE+N3yho7kb5EP56pzjW8=";
  };
}

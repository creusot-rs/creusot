{
  pkgs,
  version,
  sha256,
}:
pkgs.z3.overrideAttrs {
  inherit version;

  src = pkgs.fetchFromGitHub {
    owner = "Z3Prover";
    repo = "z3";
    rev = "z3-${version}";
    hash = sha256;
  };
}

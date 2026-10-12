{
  # Previous overlay
  z3,

  # Librairies
  fetchFromGitHub,

  # Pins
  sha256,
  version,
}:

(z3.override {
  javaBindings = false;
  ocamlBindings = false;
  pythonBindings = false;
}).overrideAttrs
  {
    inherit version;

    src = fetchFromGitHub {
      owner = "Z3Prover";
      repo = "z3";
      rev = "z3-${version}";
      hash = sha256;
    };
  }

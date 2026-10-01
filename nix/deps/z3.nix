{
  # Previous overlay
  z3,

  # Librairies
  fetchFromGitHub,

  # Pins
  sha256,
  version,
}:

# `*Bindings` are arguments of the upstream package function, not derivation
# attributes: `overrideAttrs` would leave `cmakeFlags` untouched, so they have
# to be disabled with `override` for the cmake options to be honoured.
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

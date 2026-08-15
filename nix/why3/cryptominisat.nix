{
  # Previous overlay
  cryptominisat,

  # Librairies
  fetchFromGitHub,
}:

cryptominisat.overrideAttrs {
  version = "5.8.0";

  src = fetchFromGitHub {
    owner = "msoos";
    repo = "cryptominisat";
    rev = "5.8.0";
    hash = "sha256-oGDsEYU9yXmHfbK4LyFzuJdfKHiFbSrT5PdY6GnrFQI=";
  };

  cmakeFlags = [
    "-DCMAKE_POLICY_VERSION_MINIMUM=3.5"
    "-DENABLE_PYTHON_INTERFACE=0"
  ];

  patchPhase = ''
    sed -i -e '28i#include <cstdint>' src/ccnr.h
  '';
}

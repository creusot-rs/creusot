{
  # Librairies
  darwin,
  fetchurl,
  lib,
  ocamlPackages,
  stdenv,

  # Pins
  sha256,
  version,
}:

let
  pname = "alt-ergo";
  version = "dev";

  src = fetchurl {
    url = "https://github.com/Halbaroth/alt-ergo/archive/7519aa3481fe3bb302bc95fb414281b0c2178d35.tar.gz";
    hash = "sha256-GT6XAnRkD/YPDNT1oAzi+iFf6eCiE+K6R7qalYGU4wc=";
  };
in

let
  alt-ergo-lib = ocamlPackages.buildDunePackage {
    inherit version src;
    pname = "alt-ergo-lib";

    nativeBuildInputs = with ocamlPackages; [ crunch ];
    buildInputs = with ocamlPackages; [ ppx_blob ];
    propagatedBuildInputs = with ocamlPackages; [
      camlzip
      dolmen_loop
      dune-build-info
      fmt
      ocplib-simplex
      ppx_deriving
      seq
      stdlib-shims
      zarith
    ];
  };
in

ocamlPackages.buildDunePackage {
  inherit pname version src;

  nativeBuildInputs = [
    ocamlPackages.menhir
  ]
  ++ lib.optionals stdenv.hostPlatform.isDarwin [ darwin.sigtool ];

  propagatedBuildInputs =
    (with ocamlPackages; [
      cmdliner
      dune-site
      fmt
      ppxlib
    ])
    ++ [ alt-ergo-lib ];

  outputs = [
    "bin"
    "out"
  ];

  installPhase = ''
    runHook preInstall
    dune install --prefix $bin ${pname}
    mkdir -p $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib
    mv $bin/lib/alt-ergo $out/lib/ocaml/${ocamlPackages.ocaml.version}/site-lib/
    runHook postInstall
  '';

  meta = {
    description = "High-performance theorem prover and SMT solver";
    homepage = "https://alt-ergo.ocamlpro.com/";
    license = lib.licenses.ocamlpro_nc;
  };
}

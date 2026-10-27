{
  # Previous overlay
  z3,

  # Librairies
  fetchFromGitHub,
  writeText,

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

    patches = [];

    postPatch = ''
      cp ${writeText "fix-pkg-config-paths.patch" ''
        libdir=@CMAKE_INSTALL_LIBDIR@
        includedir=@CMAKE_INSTALL_INCLUDEDIR@

        Name: z3
        Description: The Z3 Theorem Prover
        Version: @Z3_VERSION@

        Requires.private: @Z3_PKGCONFIG_REQUIRES_PRIVATE@
        Libs: -L$${libdir} -l$<TARGET_FILE_BASE_NAME:z3::libz3>
        Libs.private: @Z3_PKGCONFIG_LIBS_PRIVATE@
        Cflags: -I$${includedir}
      ''} z3.pc.cmake.in
    '';
  }

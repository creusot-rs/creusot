{
  pkgs,
  version,
  sha256,
  why3,
}:
with pkgs;
with ocamlPackages; let
  why3find = buildDunePackage {
    inherit version;

    pname = "why3find";

    src = pkgs.fetchurl {
      url = "https://git.frama-c.com/pub/why3find/-/archive/${version}/why3find-${version}.tar.gz";
      hash = sha256;
    };

    buildInputs = [
      dune-site
      dune_3
      terminal_size
      why3
      yojson
      zeromq
      zmq
    ];
  };
in
  (pkgs.writeShellScriptBin "why3find" ''
    CMD=$1; shift
    FOLDER=$(mktemp -d)

    mkdir $FOLDER/creusot
    [[ -v CREUSOT_PRELUDE ]] && find $CREUSOT_PRELUDE/creusot -name "*.coma" -exec cp {} $FOLDER/creusot \;
    ln -s $(pwd)/verif $FOLDER
    ln -s $(pwd)/why3find.json $FOLDER

    ${why3find}/bin/why3find $CMD --root $FOLDER $@

    rm -rf $FOLDER
  '').overrideAttrs({
    passthru = { inherit why3find; };
  })

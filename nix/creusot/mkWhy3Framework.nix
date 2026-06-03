{
  # Dependencies
  creusot,

  # Librairies
  symlinkJoin,
  writeTextFile,
}:

# Arguments
{
  isFree,
}:
let
  solvers =
    with creusot;
    (if isFree then [ alt-ergo-free ] else [ alt-ergo ])
    ++ [
      cvc4
      cvc5
      why3
      why3find
      z3
    ];

  why3json = writeTextFile {
    destination = "/why3find.json";
    name = "why3find.json";
    text = builtins.readFile ../../why3find.json;
  };

  creusotWhy3Conf = writeTextFile {
    destination = "/creusot_why3.conf";
    name = "creusot_why3.conf";
    text = builtins.readFile ../../creusot-install/creusot_why3.conf;
  };
in
symlinkJoin {
  name = "creusot-why3";
  paths = solvers ++ [ why3json creusotWhy3Conf ];
  postBuild = "ln -s $out $out/creusot";

  passthru = builtins.listToAttrs (
    map (drv: {
      name = drv.pname;
      value = drv;
    }) solvers
  );
}

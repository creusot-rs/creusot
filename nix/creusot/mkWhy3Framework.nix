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
in
symlinkJoin {
  name = "creusot-why3";
  paths = solvers ++ [ why3json ];
  postBuild = "ln -s $out $out/creusot";
}

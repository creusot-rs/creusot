{
  # Previous overlay
  symfpu,

  # Librairies
  fetchFromGitHub,
}:

symfpu.overrideAttrs {
  version = "0-unstable-2019-05-17";

  src = fetchFromGitHub {
    owner = "martin-cs";
    repo = "symfpu";
    rev = "8fbe139bf0071cbe0758d2f6690a546c69ff0053";
    hash = "sha256-ONGfvJMo/HXlbxHmkFs9O5nhs6aDM+XuNSPgY+ykxck=";
  };
}

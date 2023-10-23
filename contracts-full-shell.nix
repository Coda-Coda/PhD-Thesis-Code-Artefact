let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-unstable-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/51d906d2341c9e866e48c2efcaac0f2d70bfd43e.tar.gz";
  sha256 = "16nmvxfiyna5y9gwd2i3bhkpbn0nn37i481g53zc0ycw67k268sv";
}) {}; in

let deepsea = ./DeepSEA; in

let dependencies = import (deepsea + "/dependencies.nix"); in

pkgs.mkShell {
  name = "DeepSEA-env";
  buildInputs = with pkgs; [
    coq_8_14
    coqPackages_8_14.coqide
    dependencies.other
    dependencies.dsc
  ];

  shellHook = ''
    export PATH=$PATH:$PWD/DeepSEA/scripts/
  '';
}
let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/61ac4169922ca62d00bfe7f28dae6e1f27fd9c89.tar.gz";
  sha256 = "05rjb4xx2m2qqp94x39k8mv447njvyqv1zk6kshkg0j9q4hcq8lf";
}) {}; in

let deepsea = ./DeepSEA; in

let dependencies = import (deepsea + "/dependencies.nix"); in

pkgs.mkShell {
  name = "DeepSEA-env";
  buildInputs = with pkgs; [
    coq_8_14
    #coqPackages_8_14.coqide
    dependencies.other
    dependencies.dsc
  ];

  shellHook = ''
    export PATH=$PATH:$PWD/DeepSEA/scripts/
  '';
}
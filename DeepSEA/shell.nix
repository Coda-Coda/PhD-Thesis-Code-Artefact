let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/61ac4169922ca62d00bfe7f28dae6e1f27fd9c89.tar.gz";
  sha256 = "05rjb4xx2m2qqp94x39k8mv447njvyqv1zk6kshkg0j9q4hcq8lf";
}) {}; in

let dependencies = (import ./dependencies.nix); in

pkgs.mkShell {
  name = "DeepSEA-env";
  buildInputs = with pkgs; [ 
      dependencies.other
      dependencies.proving
      dependencies.dsc
      dependencies.documentation
      dependencies.unittests
      dependencies.conflux-unittests    
    ];

  shellHook = ''
    export PATH=$PATH:$PWD/scripts/
  '';
}
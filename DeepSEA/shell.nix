let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-unstable-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/51d906d2341c9e866e48c2efcaac0f2d70bfd43e.tar.gz";
  sha256 = "16nmvxfiyna5y9gwd2i3bhkpbn0nn37i481g53zc0ycw67k268sv";
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
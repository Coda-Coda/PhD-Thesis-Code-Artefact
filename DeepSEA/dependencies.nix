let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/61ac4169922ca62d00bfe7f28dae6e1f27fd9c89.tar.gz";
  sha256 = "05rjb4xx2m2qqp94x39k8mv447njvyqv1zk6kshkg0j9q4hcq8lf";
}) {}; in

let pkgsForNodeJS = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/f540aeda6f677354f1e7144ab04352f61aaa0118.tar.gz";
  sha256 = "111x41crq2kyx62a5mrqfk3f0r3m4i4p6dmj4jbpfjn5cdsgbxsr";
}) {}; in

let pkgsOldForMenhir = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/b199038e38f8b97239d1e80dc373fa9b0fd3194d.tar.gz";
  sha256 = "00iiypj3l8gc295syv00m1f21n8m1hw9rvgxjwjnpdnr1nnwjq5d";
}) {}; in

{
  other = (with pkgs; [
    gnumake
    git
    ncurses
    (pkgs.writeShellScriptBin "gsed" "exec -a $0 ${gnused}/bin/sed $@")
  ]);
  proving = (with pkgs; [
    coq_8_14
  ]);
  dsc = (with pkgs; [
    # For dsc/Edsger
    ocaml-ng.ocamlPackages_4_12.core
    ocaml-ng.ocamlPackages_4_12.dune_2
    ocaml-ng.ocamlPackages_4_12.ocaml
    ocaml-ng.ocamlPackages_4_12.findlib
    ocaml-ng.ocamlPackages_4_12.utop
    ocaml-ng.ocamlPackages_4_12.cryptokit
    ocaml-ng.ocamlPackages_4_12.ocamlbuild
    ocaml-ng.ocamlPackages_4_12.cppo
    ocaml-ng.ocamlPackages_4_12.ocaml_extlib
    ocaml-ng.ocamlPackages_4_12.yojson
    pkgsOldForMenhir.ocaml-ng.ocamlPackages_4_12.menhir
    ocaml-ng.ocamlPackages_4_12.zarith
    ]);
  documentation = (with pkgs; 
    [ mkdocs ]);
  unittests = (with pkgs; [
    pkgsForNodeJS.nodejs-16_x-openssl_1_1
  ]);
  conflux-unittests = (with pkgs; [
    # For conflux tests for the ANT blockchain
    cargo 
    openssl
    cmake
    pkg-config
  ]);
}
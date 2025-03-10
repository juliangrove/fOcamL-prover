let nixpkgs_source = (fetchTarball https://github.com/NixOS/nixpkgs/archive/nixos-24.11.tar.gz);
in
{ pkgs ? import nixpkgs_source {
    inherit system;
  }
, system ? builtins.currentSystem
}:
pkgs.stdenv.mkDerivation {
  name = "ocaml-env";
  buildInputs = with pkgs.ocamlPackages; [
    dune_3
    findlib
    pkgs.ocaml
    ocamlbuild
    ocp-indent
    merlin
    utop
  ];
}


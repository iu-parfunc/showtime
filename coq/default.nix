# Adapted from https://github.com/coq-community/manifesto/wiki/Continuous-Integration-with-Nix/ed232957a8e84a680ded4f96edaf3b9a8f17326f#simpler-setup-when-not-testing-coqs-development-branch

{ pkgs ? (import <nixpkgs> {}), shell ? false }:

with pkgs.coqPackages_8_9;

pkgs.stdenv.mkDerivation {

  name = "showtime";

  propagatedBuildInputs = [
    coq
  ];

  src = if shell then null else ./.;

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
}

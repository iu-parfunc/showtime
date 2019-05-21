# Adapted from https://github.com/coq-community/manifesto/wiki/Continuous-Integration-with-Nix/ed232957a8e84a680ded4f96edaf3b9a8f17326f#simpler-setup-when-not-testing-coqs-development-branch

{ rev    ? "650a295621b27c4ebe0fa64a63fd25323e64deb3"
, sha256 ? "0rxjkfiq53ibz0rzggvnp341b6kgzgfr9x6q07m2my7ijlirs2da"
, pkgs   ? import (builtins.fetchTarball {
             url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
             inherit sha256; }) {}
, mmaps  ? import ./deps/mmaps/default.nix { inherit pkgs; }
, shell  ? false
}:

with pkgs.coqPackages_8_8;

pkgs.stdenv.mkDerivation {

  name = "showtime";

  propagatedBuildInputs = [
    coq
    mmaps
    QuickChick
  ];

  src = if shell then null else ./.;

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
}

{ pkgs }:

with pkgs.coqPackages_8_8;

pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-mmaps";

  src = pkgs.fetchFromGitHub {
    owner  = "RyanGlScott";
    repo   = "coq-mmaps";
    rev    = "c15492584b32f1deb8bb78b5ef807eceddb5f188";
    sha256 = "026rxwqr6x11z8jpn0ibarl7jcjg2ld4ab0vly22y442n3avm5sl";
  };

  buildInputs = [ coq ];

  installPhase = ''
    make -f Makefile.coq COQLIB=$out/lib/coq/${coq.coq-version}/ install
  '';

  meta = with pkgs.stdenv.lib; {
    homepage    = https://github.com/RyanGlScott/coq-mmaps;
    description = "Modular Finite Maps overs Ordered Types";
    maintainers = [ ];
    platforms   = coq.meta.platforms;
  };
}

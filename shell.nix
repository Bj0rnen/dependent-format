with (import <nixpkgs> {}).pkgs;
let
  ghcPackages = haskell.packages.ghc844;
  ghc = ghcPackages.ghcWithPackages
          (pkgs: with pkgs; [ singletons exinst constraints generics-sop ]);
in
stdenv.mkDerivation {
  name = "my-haskell-env-0";
  buildInputs = [ ghc atom which ghcPackages.ghcid ];
  shellHook = "eval $(grep export ${ghc}/bin/ghc)";
}

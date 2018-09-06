with (import <nixpkgs> {}).pkgs;
let
  ghcPackages = haskell.packages.ghc843;
  ghc = ghcPackages.ghcWithPackages
          (pkgs: with pkgs; [ singletons constraints exinst ]);
in
stdenv.mkDerivation {
  name = "my-haskell-env-0";
  buildInputs = [ ghc atom which ghcPackages.ghcid ];
  shellHook = "eval $(grep export ${ghc}/bin/ghc)";
}

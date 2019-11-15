with (import <nixpkgs> {}).pkgs;
let
  ghcPackages = haskell.packages.ghc865;

  # I've modified nixpkgs, so that singletons_2_5 depends on th-desugar_1_9,
  # and exinst_0_7 depends on singletons_2_5. (just singletons depending on th-desugar_1_9,
  # would have probably accomplished it too).
  # I've tried to figure out how to use overlays to make that change local to this shell.nix
  # But I don't know how to use that feature correctly...

  #config = {
  #  packageOverrides = pkgs: rec {
  #    haskellPackages = pkgs.haskellPackages.override {
  #      overrides = self: super: {
  #        singletons = super.singletons_2_5;
  #      };
  #    };
  #  };
  #};

  #config = {
  #  haskell.packages.ghc862 = pkgs.haskell.packages.ghc862.override {
  #    overrides = self: super: {
  #      singletons = super.singletons_2_5;
  #    };
  #  };
  #};

  #newPkgs = import <nixpkgs> { inherit config; };
  #ghcPackages = newPkgs.haskell.packages.ghc862;


  ghc = ghcPackages.ghcWithPackages
          (pkgs: with pkgs; [ singletons constraints kind-generics kind-generics-th indexed-extras do-notation ]);
in
stdenv.mkDerivation {
  name = "my-haskell-env-0";
  buildInputs = [ ghc atom which ghcPackages.ghcid ];
  shellHook = "eval $(grep export ${ghc}/bin/ghc)";
}

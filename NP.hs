{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingVia #-}

-- Unused code lifted out of main file. Not clear if there's a point in keeping this around.
module NP where

import Data.Singletons
import GHC.TypeNats
import Data.Singletons.TypeLits

import Generics.SOP hiding (Sing, Nil, SingI, sing)
import Unsafe.Coerce

import Data.Kind.Fin (ifZeroElse)

type family
    Lookup (i :: Nat) (xs :: [a]) :: a where
    Lookup 0 (a ': _ ) = a
    Lookup i (_ ': as) = Lookup (i-1) as
type family
    Update (i :: Nat) (a :: k) (xs :: [k]) :: [k] where
    Update 0 a (_ ': xs) = (a ': xs)
    Update i a (x ': xs) = x ': Update (i-1) a xs

lookupNP :: forall i ts. Sing i -> NP I ts -> Lookup i ts
lookupNP SNat (I a :* as) =
    ifZeroElse @i a (\(Proxy :: Proxy i1) -> unsafeCoerce $ lookupNP (sing @i1) as)
updateNP :: forall i ts a. Sing i -> a -> NP I ts -> NP I (Update i a ts)
updateNP SNat a (I x :* xs) =
    ifZeroElse @i (I a :* xs) (\(Proxy :: Proxy i1) -> unsafeCoerce $ I x :* updateNP (sing @i1) a xs)

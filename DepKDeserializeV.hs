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

module DepKDeserializeV where

import Serialize
import Vector
import DepState
import Knowledge

import Data.Singletons
import Data.Singletons.TH
import GHC.TypeNats
import Data.Singletons.TypeLits
import Data.Kind

import qualified GHC.Generics as GHC hiding (from, to)
import Generics.SOP hiding (Sing, Nil, SingI, sing)
import qualified Generics.SOP as SOP
import Generics.SOP.Classes (Same)
import GHC.TypeLits (TypeError(..), ErrorMessage(..))
import           Generics.Kind hiding (Nat, (:~:))
import qualified Generics.Kind as K
import Generics.Kind.TH

import Data.Proxy
import Data.Constraint
import Unsafe.Coerce
import GHC.Types (Any)
import Data.Coerce
import Data.Functor.Const

import Data.Word
import Data.Bits
import Numeric.Natural
import Data.Kind.Fin (ltNat, predecessor, subNat)
import Data.Singletons.Fin

import Data.Reflection

{-
data PartiallyKnown (f :: ks) (ds :: DepStateList ks) where
    PartiallyKnown :: ExplicitPartialKnowledge ks xs ds -> f :@@: xs -> PartiallyKnown f ds

class DepKDeserializeV (f :: ks) where
    type DepStateReqs (f :: ks) (ds :: DepStateList ks) :: Constraint
    type TaughtBy (f :: ks) :: DepStateList ks
    depKDeserializeV :: DepStateReqs f ds => ExplicitPartialKnowledge ks xs ds -> [Word8] -> (PartiallyKnown f (TaughtBy f), [Word8])
-}


data DepStateList ds where
    DZ :: DepStateList Type
    DS :: DepState -> DepStateList xs -> DepStateList (x -> xs)

data ExplicitPartialKnowledge (xs :: LoT ks) (ds :: DepStateList ks) where
    ExplicitPartialKnowledgeNil  :: ExplicitPartialKnowledge LoT0 'DZ
    ExplicitPartialKnowledgeCons :: Knowledge d (x :: a) -> ExplicitPartialKnowledge xs ds -> ExplicitPartialKnowledge (x :&&: xs) ('DS d ds)

data SomePartialKnowledge (ds :: DepStateList ks) where
    SomePartialKnowledge :: ExplicitPartialKnowledge xs ds -> SomePartialKnowledge ds

--data PartiallyKnown (f :: LoT ks -> Type) (ds :: DepStateList ks) where
--    PartiallyKnown :: ExplicitPartialKnowledge xs ds -> f xs -> PartiallyKnown f ds

class DepKDeserializeV (f :: ks) (a :: Atom ls ks) where
    type DepStateReqs (f :: ks) (a :: Atom ls ks) (ds :: DepStateList ls) :: Constraint
    type TaughtBy (f :: ks) (a :: Atom ls ks) :: DepStateList ls
    idunnolol :: forall (x :: ks -> Type) (xs :: LoT ls). Field (Kon x :@: a) xs
    --depKDeserializeV :: [Word8] -> (f xs, SomePartialKnowledge ?, [Word8])

instance DepKDeserializeV (Sing :: Nat -> Type) (Var3 :: Atom (k0 -> k1 -> k2 -> (Nat -> Type) -> Type) (Nat -> Type))

--_foo :: forall (f :: ks) (a :: Atom ks Type). Int
--_foo = undefined

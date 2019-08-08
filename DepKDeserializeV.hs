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
{-# LANGUAGE LambdaCase #-}

module DepKDeserializeV where

import Serialize
import Vector
import DepState
import Knowledge
import DepLevel

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

import Control.Monad.State

{-
data PartiallyKnown (f :: ks) (ds :: DepStateList ks) where
    PartiallyKnown :: ExplicitPartialKnowledge ks xs ds -> f :@@: xs -> PartiallyKnown f ds

class DepKDeserializeV (f :: ks) where
    type DepStateReqs (f :: ks) (ds :: DepStateList ks) :: Constraint
    type TaughtBy (f :: ks) :: DepStateList ks
    depKDeserializeV :: DepStateReqs f ds => ExplicitPartialKnowledge ks xs ds -> [Word8] -> (PartiallyKnown f (TaughtBy f), [Word8])
-}


{-
data ExplicitPartialKnowledge (xs :: LoT ks) (ds :: DepStateList ks) where
    ExplicitPartialKnowledgeNil  :: ExplicitPartialKnowledge LoT0 'DZ
    ExplicitPartialKnowledgeCons :: Knowledge d (x :: a) -> ExplicitPartialKnowledge xs ds -> ExplicitPartialKnowledge (x :&&: xs) ('DS d ds)

data SomePartialKnowledge (ds :: DepStateList ks) where
    SomePartialKnowledge :: ExplicitPartialKnowledge xs ds -> SomePartialKnowledge ds

--data PartiallyKnown (f :: LoT ks -> Type) (ds :: DepStateList ks) where
--    PartiallyKnown :: ExplicitPartialKnowledge xs ds -> f xs -> PartiallyKnown f ds

--class DepKDeserializeV (f :: ks) (a :: Atom ls ks) where
--    type DepStateReqs (f :: ks) (a :: Atom ls ks) (ds :: DepStateList ls) :: Constraint
--    type TaughtBy (f :: ks) (a :: Atom ls ks) :: DepStateList ls
--    idunnolol :: forall (x :: ks -> Type) (xs :: LoT ls). Field (Kon x :@: a) xs
--    --depKDeserializeV :: [Word8] -> (f xs, SomePartialKnowledge ?, [Word8])
--
--instance DepKDeserializeV (Sing :: Nat -> Type) (Var3 :: Atom (k0 -> k1 -> k2 -> (Nat -> Type) -> Type) (Nat -> Type))

--_foo :: forall (f :: ks) (a :: Atom ks Type). Int
--_foo = undefined

--class DepKDeserializeA (a :: Atom d ks)
--instance DepKDeserializeA (Kon (Sing :: Nat -> Type) :: Atom d (Nat -> Type))

--class DepKDeserializeA (a :: Atom ks Type)
----instance DepKDeserializeA (Kon (Sing :: Nat -> Type) :@: a0)
--instance DepKDeserializeA (Kon (Sing :: Nat -> Type) :@: Kon k0 :: Atom ks Type)
--instance DepKDeserializeA (Kon (Sing :: Nat -> Type) :@: Var v0 :: Atom ks Type)

--data Foo (a :: Atom d ks) (ds :: DepStateList d) where
--    FooNil :: Foo (Kon f) ds
--    FooCons ::

--data Args (ks :: Type) where
--    ArgsNil :: Args Type
--    ArgsCons :: Atom k Type -> Args ks -> Args (k -> ks)

class DepKDeserialize (f :: ks) where
    type DepLevels (f :: ks) :: DepLevelList ks
    depKDeserialize :: SomePartialKnowledge (ds :: DepStateList d) -> [Word8] -> (Void, [Word8])
instance DepKDeserialize (Sing :: Nat -> Type) where
    type DepLevels (Sing :: Nat -> Type) = DLS Learning DLZ
-}

data DepStateList :: Type -> Type where
    DZ :: DepStateList Type
    DS :: DepState -> DepStateList xs -> DepStateList (x -> xs)

data DepLevelList :: Type -> Type where
    DLZ :: DepLevelList Type
    DLS :: DepLevel -> DepLevelList xs -> DepLevelList (x -> xs)

data AtomList :: Type -> Type -> Type where
    AtomNil  :: AtomList d Type
    AtomCons :: Atom d k -> AtomList d ks -> AtomList d (k -> ks)


type family
    GetDepState (v :: TyVar d k) (ds :: DepStateList d) :: DepState where
    GetDepState  'VZ    ('DS d _ ) = d
    GetDepState ('VS v) ('DS _ ds) = GetDepState v ds


class DepKDeserialize (f :: ks) where
    type Require (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint
    type Learn (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d
    --depKDeserialize ::
    --    forall d (ds :: DepStateList d) (as :: AtomList d ks).
    --    KnowledgeList ds -> State [Word8] (SomeK ks f, KnowledgeList (Learn f as ds))
        -- TODO: Not sure how SomeK should look. Should maybe be like (SomeK ds as f) instead.
        -- TODO: Indexed by the same things as Learn in that case, making it seem like it could
        -- TODO: contain the whole updated KnowledgeList (or at least the means to build it) all
        -- TODO: on its own. I don't think that's something to strive for. Would be the new
        -- TODO: PartiallyKnownK.
        -- TODO: Either way, "as" showing up only in the return type can't be right...
instance (SingKind k, Serialize (Demote k)) => DepKDeserialize (Sing :: k -> Type) where
    type Require (Sing :: k -> Type) _ _ = ()

    type Learn (Sing :: k -> Type) ('AtomCons ('Kon _)       'AtomNil)        ds  = ds
    type Learn (Sing :: k -> Type) ('AtomCons ('Var  'VZ)    'AtomNil) ('DS _ ds) = ('DS 'Known ds)
    type Learn (Sing :: k -> Type) ('AtomCons ('Var ('VS v)) 'AtomNil) ('DS d ds) =
        'DS d (Learn (Sing :: k -> Type) ('AtomCons ('Var v) 'AtomNil) ds)
    --depKDeserialize = do
    --    d <- state deserialize
    --    case d of
    --        FromSing (s :: Sing (s :: k)) ->
    --            return (unsafeCoerce s)  -- TODO: This lacks the check that verifies the s is what we expected, if we had any expectation.
instance Serialize a => DepKDeserialize (Vector a :: Nat -> Type) where
    type Require (Vector a :: Nat -> Type) ('AtomCons ('Kon _) 'AtomNil) ds = ()
    type Require (Vector a :: Nat -> Type) ('AtomCons ('Var v) 'AtomNil) ds = GetDepState v ds ~ 'Known
    type Learn (Vector a :: Nat -> Type) _ ds  = ds
    --depKDeserialize =
    --    case undefined of  -- TODO: Here we need access to the knowledge.
    --        SomeSing (SNat :: Sing n) -> do
    --            (a :: Vector a :@@: (n :&&: LoT0)) <- state deserialize
    --            return (unsafeCoerce a)

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

module DepLevel where

import DepState

import Vector

import Data.Kind
import GHC.TypeLits
import Data.Singletons

import qualified GHC.Generics as GHC
import Generics.Kind

-- Requiring: (forall x. SingI x => Serialize (f x))
--     A field that's only (de)serializable when the type index is known.
--
-- NonDep:    (forall x. Serialize (f x), forall x y. Coercible (f x) (f y))
--     A field that's always (de)serializable, independently if type index.
--
-- Learning:  (Serialize (Some1 f))
--     A field that can (de)serialize without knowing the type index.
--     Deserializing recovers the type index.
data DepLevel = Requiring | NonDep | Learning

type family
    ApplyDepLevel (f :: DepLevel) (a :: DepState) :: DepState where
    ApplyDepLevel 'Requiring 'Unknown = TypeError ('Text "Required type index not known")
    ApplyDepLevel 'Requiring 'Known = 'Known
    ApplyDepLevel 'NonDep a = a
    ApplyDepLevel 'Learning _ = 'Known

type family
    ProductDepLevel (l :: DepLevel) (r :: DepLevel) :: DepLevel where
    ProductDepLevel 'Requiring 'Requiring = 'Requiring
    ProductDepLevel 'Requiring 'NonDep    = 'Requiring
    ProductDepLevel 'Requiring 'Learning  = 'Requiring
    ProductDepLevel 'NonDep    'Requiring = 'Requiring
    ProductDepLevel 'NonDep    'NonDep    = 'NonDep
    ProductDepLevel 'NonDep    'Learning  = 'Learning
    ProductDepLevel 'Learning  'Requiring = 'Learning
    ProductDepLevel 'Learning  'NonDep    = 'Learning
    ProductDepLevel 'Learning  'Learning  = 'Learning

class HasDepLevel (f :: k -> Type) where
    type DepLevelOf f :: DepLevel
    --type DepLevelOf f = DepLevelOf (GHC.Rep1 f)
    type DepLevelOf f = DepLevelOf (RepK f)
-- GHC.Generic instances
instance HasDepLevel GHC.U1 where
    type DepLevelOf GHC.U1 = 'NonDep
instance HasDepLevel (GHC.Rec0 c) where
    type DepLevelOf (GHC.Rec0 c) = 'NonDep
instance HasDepLevel (GHC.K1 i c) where
    type DepLevelOf (GHC.K1 i c) = 'NonDep
instance HasDepLevel (GHC.Rec1 f) where
    type DepLevelOf (GHC.Rec1 f) = DepLevelOf f
instance HasDepLevel (GHC.S1 c f) where
    type DepLevelOf (GHC.S1 c f) = DepLevelOf f
instance HasDepLevel (GHC.M1 i c f) where
    type DepLevelOf (GHC.M1 i c f) = DepLevelOf f
instance HasDepLevel (l GHC.:*: r) where
    type DepLevelOf (l GHC.:*: r) = ProductDepLevel (DepLevelOf l) (DepLevelOf r)
--
instance HasDepLevel Sing where
    type DepLevelOf Sing = 'Learning
instance HasDepLevel (Vector a) where
    type DepLevelOf (Vector a) = 'Requiring

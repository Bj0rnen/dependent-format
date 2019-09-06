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
{-# LANGUAGE RoleAnnotations #-}

module DepKDeserializeWordTest where

import DepKDeserializeWord
import DepKDeserialize
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


data L0Word64 (size :: PWord64) = L0Word64
    { size :: Sing size
    } deriving (Show, GHC.Generic)
instance GenericK L0Word64 (size :&&: 'LoT0) where
    type RepK L0Word64 = Field (Sing :$: Var0)
instance GenericK (L0Word64 size) 'LoT0 where
    type RepK (L0Word64 size) = Field ('Kon (Sing size))
deriving instance DepKDeserialize L0Word64

testL0Word64 :: String
testL0Word64 =
    case evalState
            (depKDeserialize @_ @L0Word64 (Proxy @('AtomCons Var0 'AtomNil)) (KnowledgeCons KnowledgeU KnowledgeNil))
            [0,1,2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a


data L0R0Word16 (size :: PWord16) = L0R0Word16
    { size :: Sing size
    , vec  :: GeneralizedVector Word8 size
    } deriving (Show, GHC.Generic)
instance GenericK L0R0Word16 (size :&&: 'LoT0) where
    type RepK L0R0Word16 = Field (Sing :$: Var0) :*: Field (GeneralizedVector Word8 :$: Var0)
instance GenericK (L0R0Word16 size) 'LoT0 where
    type RepK (L0R0Word16 size) = Field ('Kon (Sing size)) :*: Field ('Kon (GeneralizedVector Word8 size))
deriving instance DepKDeserialize L0R0Word16

testL0R0Word16 :: String
testL0R0Word16 =
    case evalState
            (depKDeserialize @_ @L0R0Word16 (Proxy @('AtomCons Var0 'AtomNil)) (KnowledgeCons KnowledgeU KnowledgeNil))
            [0,1,2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

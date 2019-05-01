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

module Generic1KTest where

import Generic1K

import Serialize
import Vector
import Product1Serialize
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

import Exinst
import Data.Reflection


data DependentPair (size :: Nat) = DependentPair
    { size :: Sing size
    , arr :: Vector Word8 size
    } deriving (Show, GHC.Generic1)

lol :: GHC.Rep1 DependentPair 2
lol = GHC.from1 (DependentPair SNat (1 :> 2 :> Nil))

slol = serialize lol
dlol :: (GHC.Rep1 DependentPair 2, [Word8])
dlol = deserialize [2, 1, 2]

lol' :: DependentPair 2
lol' = GHC.to1 (fst dlol)

instance Serialize (Some1 DependentPair) where
    serialize (Some1 SNat (DependentPair SNat arr)) = serialize arr
    deserialize bs =
        case deserialize bs of
            (FromSing (SNat :: Sing (size :: Nat)), bs') ->
                case deserialize bs' of
                    (arr :: Vector Word8 size, bs'') ->
                        (Some1 SNat (DependentPair SNat arr), bs'')

someLol :: Some1 (GHC.Rep1 DependentPair)
someLol = Some1 SNat $ GHC.from1 (DependentPair SNat (1 :> 2 :> Nil))
sdp = serialize someLol

data UseSizeManyTimes (size :: Nat) = UseSizeManyTimes
    { whatever :: Word8
    , size :: Sing size
    , arr1 :: Vector Word8 size
    , sizeAgain :: Sing size
    , whatever2 :: Word8
    , arr2 :: Vector Word16 size
    , arr3 :: Vector Word8 size
    , sizeAgainAgain :: Sing size
    } deriving (GHC.Generic1, Show)

someUST :: Some1 UseSizeManyTimes
someUST = Some1 SNat $ UseSizeManyTimes 123 SNat (1 :> 2 :> 3 :> Nil) SNat 42 (4 :> 5 :> 6 :> Nil) (7 :> 8 :> 9:> Nil) SNat
sust = serializeSome1 someUST

dust :: Some1 UseSizeManyTimes
dust = fst $ deserializeSome1 [123,3,1,2,3,3,42,0,4,0,5,0,6,7,8,9,3]

dust2 :: Some1 UseSizeManyTimes
dust2 = fst $ deserializeSome1 [0,0,0,0,0]


data NeverUseSize (size :: Nat) = NeverUseSize
    { x :: Word8
    , y :: Word8
    } deriving (GHC.Generic1, Show, HasDepLevel)
      deriving Serialize via (Generic1Wrapper NeverUseSize size)

dnus :: NeverUseSize a
dnus = fst $ deserialize [1, 2]
snus :: [Word8]
snus = serialize dnus


data RequiringSize (size :: Nat) = RequiringSize
    { arr1 :: Vector Word8 size
    , arr2 :: Vector Word8 size
    } deriving (Show, HasDepLevel, GHC.Generic)
      deriving Serialize via (GenericKWrapper RequiringSize (size :&&: LoT0))
instance GenericK RequiringSize (size :&&: LoT0) where
    type RepK RequiringSize = Field (Vector Word8 :$: Var0) :*: Field (Vector Word8 :$: Var0)
--instance Split (RequiringSize size) RequiringSize (size :&&: LoT0)
srs :: [Word8]
srs = serialize $ RequiringSize (1 :> 2 :> 3 :> Nil) (4 :> 5 :> 6 :> Nil)
drs :: KnownNat size => (RequiringSize size, [Word8])
drs = deserialize srs

data ProvidingSize (size :: Nat) = ProvidingSize
    { uws :: UnitWithSize size
    , size :: Sing size
    , rs :: RequiringSize size
    } deriving (Show, HasDepLevel, GHC.Generic)
      deriving Serialize via (GenericKWrapper ProvidingSize (size :&&: LoT0))
instance GenericK ProvidingSize (size :&&: LoT0) where
    type RepK ProvidingSize = Field (UnitWithSize :$: Var0) :*: Field (Sing :$: Var0) :*: Field (RequiringSize :$: Var0)
--instance Split (ProvidingSize size) ProvidingSize (size :&&: LoT0)
sps :: [Word8]
sps = serialize $ ProvidingSize UnitWithSize SNat (RequiringSize (1 :> 2 :> 3 :> Nil) (4 :> 5 :> 6 :> Nil))
dps :: Some1 ProvidingSize
dps = fst $ deserializeSome1K sps
dps' :: KnownNat size => ProvidingSize size
dps' = fst $ deserialize sps

data IgnoringSize (size :: Nat) = IgnoringSize
    { size :: Word8
    } deriving (Show, HasDepLevel, GHC.Generic)
      deriving Serialize via (GenericKWrapper IgnoringSize (size :&&: LoT0))
instance GenericK IgnoringSize (size :&&: LoT0) where
    type RepK IgnoringSize = Field (Kon Word8)
--instance Split (IgnoringSize size) IgnoringSize (size :&&: LoT0)
sis :: [Word8]
sis = serialize $ IgnoringSize 123
dis :: IgnoringSize size
dis = fst $ deserialize sis

data UnitWithSize (size :: Nat) = UnitWithSize
    {} deriving (Show, HasDepLevel, GHC.Generic)
       deriving Serialize via (GenericKWrapper UnitWithSize (size :&&: LoT0))
instance GenericK UnitWithSize (size :&&: LoT0) where
    type RepK UnitWithSize = U1
--instance Split (UnitWithSize size) UnitWithSize (size :&&: LoT0)
snws :: [Word8]
snws = serialize $ UnitWithSize
dnws :: UnitWithSize size
dnws = fst $ deserialize snws

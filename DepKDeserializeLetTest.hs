{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module DepKDeserializeLetTest where

import DepKDeserialize
import DepKDeserializeLet
import Vector

import Data.Singletons.TH
import GHC.TypeNats
import Data.Singletons.TypeLits

import Generics.Kind.TH

import Data.Constraint
import Data.Constraint.Nat

import Data.Word

import Control.Monad.State
import Control.Monad.Except


(%+) :: Sing n -> Sing m -> Sing (n + m)
(SNat :: Sing n) %+ (SNat :: Sing m) = SNat \\ plusNat @n @m
$(genDefunSymbols [''(+)])


$(singletons [d|
  onePlus :: Nat -> Nat
  onePlus a = 1 + a
  |])

data RecordWithOnePlus = forall (a :: Nat) (b :: Nat). RecordWithOnePlus
    { a :: Sing a
    , b :: Let OnePlusSym0 a b
    , v :: Vector Word8 b
    }
deriving instance Show RecordWithOnePlus
$(deriveGenericK ''RecordWithOnePlus)

deriving instance DepKDeserialize RecordWithOnePlus

testRecordWithOnePlus :: (Either DeserializeError RecordWithOnePlus, [Word8])
testRecordWithOnePlus = runState (runExceptT $ deserialize @RecordWithOnePlus) [1,2,3,4,5,6]

$(singletons [d|
  plus :: Nat -> Nat -> Nat
  plus a b = a + b
  |])

data RecordWithPlus = forall (a :: Nat) (b :: Nat) (f :: Nat ~> Nat) (c :: Nat). RecordWithPlus
    { a :: Sing a
    , b :: Sing b
    , f :: Let PlusSym0 a f
    , c :: Let f b c
    , v :: Vector Word8 c
    }
deriving instance Show RecordWithPlus
$(deriveGenericK ''RecordWithPlus)

deriving instance DepKDeserialize RecordWithPlus

testRecordWithPlus :: (Either DeserializeError RecordWithPlus, [Word8])
testRecordWithPlus = runState (runExceptT $ deserialize @RecordWithPlus) [1,2,3,4,5,6]


data RecordWithPlus2 = forall (a :: Nat) (b :: Nat) (c :: Nat). RecordWithPlus2
    { a :: Sing a
    , b :: Sing b
    , c :: Let2 PlusSym0 a b c
    , v :: Vector Word8 c
    }
deriving instance Show RecordWithPlus2
$(deriveGenericK ''RecordWithPlus2)

deriving instance DepKDeserialize RecordWithPlus2

testRecordWithPlus2 :: (Either DeserializeError RecordWithPlus2, [Word8])
testRecordWithPlus2 = runState (runExceptT $ deserialize @RecordWithPlus2) [1,2,3,4,5,6]


data RecordWithPlus2Contradictory = RecordWithPlus2Contradictory
    { c :: Let2 PlusSym0 1 2 4
    }
deriving instance Show RecordWithPlus2Contradictory
$(deriveGenericK ''RecordWithPlus2Contradictory)

deriving instance DepKDeserialize RecordWithPlus2Contradictory

testRecordWithPlus2Contradictory :: (Either DeserializeError RecordWithPlus2Contradictory, [Word8])
testRecordWithPlus2Contradictory = runState (runExceptT $ deserialize @RecordWithPlus2Contradictory) [1,2,3,4,5,6]

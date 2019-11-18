{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
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

module DepKDeserializeWordTest where

import DepKDeserializeWord
import DepKDeserialize
import DepKDeserializeLet
import Vector
import Knowledge

import Data.Singletons.TypeLits

import           Generics.Kind hiding (Nat, (:~:))
import Generics.Kind.TH

import Data.Word
import Data.Int

import Control.Monad.State
import Control.Monad.Indexed.State


data L0Word64 (size :: Promoted Word64) = L0Word64
    { size :: Sing size
    } deriving (Show)
$(deriveGenericK ''L0Word64)

deriving instance DepKDeserialize L0Word64

testL0Word64 :: String
testL0Word64 =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @L0Word64 (Proxy @('AtomCons Var0 'AtomNil)))
            (KnowledgeCons KnowledgeU KnowledgeNil, [0,1,2,3,4,5,6,7]) of
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a


data L0R0Word16 (size :: Promoted Word16) = L0R0Word16
    { size :: Sing size
    , vec  :: GeneralizedVector Word8 size
    } deriving (Show)
$(deriveGenericK ''L0R0Word16)

deriving instance DepKDeserialize L0R0Word16

testL0R0Word16 :: String
testL0R0Word16 =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @L0R0Word16 (Proxy @('AtomCons Var0 'AtomNil)))
            (KnowledgeCons KnowledgeU KnowledgeNil, [0,1,2,3,4,5,6,7]) of
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a


data RecordWithWordToNat = forall (a :: Promoted Word32) (b :: Nat). RecordWithWordToNat
    { a :: Sing a
    , b :: Let WordToNat a b
    , v :: Vector Word8 b
    }
deriving instance Show RecordWithWordToNat
$(deriveGenericK ''RecordWithWordToNat)

deriving instance DepKDeserialize RecordWithWordToNat

testRecordWithWordToNat :: (Either DeserializeError (RecordWithWordToNat, [Word8]))
testRecordWithWordToNat = runStateT (deserialize @RecordWithWordToNat) [0,0,0,2,5,6,7]


data L0R0Word8 = forall (size :: Promoted Word8). L0R0Word8
    { size :: Sing size
    , vec  :: GVector Word16 size
    }
deriving instance Show L0R0Word8
$(deriveGenericK ''L0R0Word8)

deriving instance DepKDeserialize L0R0Word8

testL0R0Word8 :: (Either DeserializeError (L0R0Word8, [Word8]))
testL0R0Word8 = runStateT (deserialize @L0R0Word8) [3,1,2,3,4,5,6,7]


data RecordWithIntToNat = forall (a :: Promoted Int8) (b :: Nat). RecordWithIntToNat
    { a :: Sing a
    , b :: LetFromJust IntToMaybeNat a b
    , v :: Vector Word8 b
    }
deriving instance Show RecordWithIntToNat
$(deriveGenericK ''RecordWithIntToNat)

deriving instance DepKDeserialize RecordWithIntToNat

testRecordWithIntToNat :: (Either DeserializeError (RecordWithIntToNat, [Word8]))
testRecordWithIntToNat = runStateT (deserialize @RecordWithIntToNat) [3,2,5,6,7]

{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module BitMap where

import DepKDeserialize
import DepKDeserializeWord
import DepKDeserializeLet
import Generics.Kind.TH

import ASCII
import Data.Word
import Vector
import Data.Singletons.Fin
import Data.Type.Equality
import Control.Monad.State

{-
data BitMap = forall (width :: Promoted Word8) (height :: Promoted Word8). BitMap
    { bmp    :: ASCII "BMP"
    , width  :: Sing width
    , height :: Sing height
    , pixels :: GVector (GVector Word8 width) height
    }
deriving instance Show BitMap
$(deriveGenericK ''BitMap)
deriving instance DepKDeserialize BitMap

testSerializeEmpty = serialize (BitMap { width = SPromoted (SFin @256 @('Fin 0)), height = SPromoted (SFin @256 @('Fin 0)), pixels = GVector (Let Refl) Nil })
-}

import GHC.TypeNats
import Data.Singletons.TypeLits

data BitMap = forall (width :: Nat) (height :: Nat). BitMap
    { bmp    :: ASCII "BMP"
    , width  :: Sing width
    , height :: Sing height
    , pixels :: Vector (Vector Word8 0) height
    }
deriving instance Show BitMap
$(deriveGenericK ''BitMap)
deriving instance DepKDeserialize BitMap

testSerializeEmpty = serialize (BitMap { bmp = ASCII, width = (SNat @0), height = (SNat @0), pixels = Nil })
testDeserializeEmpty = runStateT (deserialize @BitMap) [66,77,80,0,0]

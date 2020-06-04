{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module BitMap where

import DepKDeserialize (DepKDeserialize, serialize, deserialize, DeserializeError)
import Generics.Kind.TH (deriveGenericK)

import DepKDeserializeWord (Promoted, GeneralizedVector(..), sWord8)
import ASCII (ASCII(..))
import Data.Word (Word8)
import Data.Singletons (WrappedSing(..))
import Vector (Vector(..))
import Control.Monad.State (StateT(..))

data BitMap = forall (width :: Promoted Word8) (height :: Promoted Word8). BitMap
    { bmp    :: ASCII "BMP"
    , width  :: WrappedSing width
    , height :: WrappedSing height
    , pixels :: GeneralizedVector (GeneralizedVector Word8 width) height
    }
deriving instance Show BitMap
$(deriveGenericK ''BitMap)
deriving instance DepKDeserialize BitMap

testSerializeEmpty :: [Word8]
testSerializeEmpty = serialize $ BitMap
    { bmp = ASCII
    , width = WrapSing (sWord8 @0)
    , height = WrapSing (sWord8 @0)
    , pixels = GeneralizedVector Nil
    }
-- | >>> testSerializeEmpty
-- [66,77,80,0,0]

testDeserializeEmpty :: Either DeserializeError (BitMap, [Word8])
testDeserializeEmpty = runStateT (deserialize @BitMap) [66,77,80,0,0]
-- | >>> testDeserializeEmpty
-- Right (BitMap {bmp = ASCII, width = SPromoted (SFin @256 @('Fin 0)), height = SPromoted (SFin @256 @('Fin 0)), pixels = GeneralizedVector Nil},[])

testSerializeNonEmpty :: [Word8]
testSerializeNonEmpty = serialize $ BitMap
    { bmp = ASCII
    , width = WrapSing (sWord8 @2)
    , height = WrapSing (sWord8 @2)
    , pixels = GeneralizedVector (GeneralizedVector (0 :> 1 :> Nil) :> GeneralizedVector (2 :> 3 :> Nil) :> Nil)
    }
-- | >>> testSerializeNonEmpty
-- [66,77,80,2,2,0,1,2,3]

testDeserializeNonEmpty :: Either DeserializeError (BitMap, [Word8])
testDeserializeNonEmpty = runStateT (deserialize @BitMap) [66,77,80,2,2,0,1,2,3]
-- | >>> testDeserializeNonEmpty
-- Right (BitMap {bmp = ASCII, width = SPromoted (SFin @256 @('Fin 2)), height = SPromoted (SFin @256 @('Fin 2)), pixels = GeneralizedVector (GeneralizedVector (0 :> (1 :> Nil)) :> (GeneralizedVector (2 :> (3 :> Nil)) :> Nil))},[])

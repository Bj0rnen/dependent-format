{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}

module BitMapComposed where

import DepKDeserialize (DepKDeserialize, serialize, deserialize, DeserializeError)
import Generics.Kind.TH (deriveGenericK)

import DepKDeserializeWord (Promoted, GeneralizedVector(..), sWord8)
import ASCII (ASCII(..))
import Data.Word (Word8)
import Data.Singletons.Fin (Sing)
import Vector (Vector(..))
import Control.Monad.State (StateT(..))

data Dimensions (width :: Promoted Word8) (height :: Promoted Word8) = Dimensions
    { width  :: Sing width
    , height :: Sing height
    } deriving (Show)
$(deriveGenericK ''Dimensions)
deriving instance DepKDeserialize Dimensions

data PixelData (width :: Promoted Word8) (height :: Promoted Word8) = PixelData
    { pixels :: GeneralizedVector (GeneralizedVector Word8 width) height
    } deriving (Show)
$(deriveGenericK ''PixelData)
deriving instance DepKDeserialize PixelData

data BitMap = forall (width :: Promoted Word8) (height :: Promoted Word8). BitMap
    { bmp        :: ASCII "BMP"
    , dimensions :: Dimensions width height
    , pixels     :: PixelData width height
    }
deriving instance Show BitMap
$(deriveGenericK ''BitMap)
deriving instance DepKDeserialize BitMap

testSerializeEmpty :: [Word8]
testSerializeEmpty = serialize  $ BitMap
    { bmp = ASCII
    , dimensions = Dimensions
        { width = sWord8 @0
        , height = sWord8 @0
        }
    , pixels = PixelData
        { pixels = GeneralizedVector Nil
        }
    }
-- > testSerializeEmpty
-- [66,77,80,0,0]

testDeserializeEmpty :: Either DeserializeError (BitMap, [Word8])
testDeserializeEmpty = runStateT (deserialize @BitMap) [66,77,80,0,0]
-- > testDeserializeEmpty
-- Right (BitMap {bmp = ASCII, dimensions = Dimensions {width = SPromoted (SFin @256 @('Fin 0)), height = SPromoted (SFin @256 @('Fin 0))}, pixels = PixelData {pixels = GeneralizedVector Nil}},[])

testSerializeNonEmpty :: [Word8]
testSerializeNonEmpty = serialize $ BitMap
    { bmp = ASCII
    , dimensions = Dimensions
        { width = sWord8 @2
        , height = sWord8 @2
        }
    , pixels = PixelData
        { pixels = GeneralizedVector (GeneralizedVector (0 :> 1 :> Nil) :> GeneralizedVector (2 :> 3 :> Nil) :> Nil)
        }
    }
-- > testSerializeNonEmpty
-- [66,77,80,2,2,0,1,2,3]

testDeserializeNonEmpty :: Either DeserializeError (BitMap, [Word8])
testDeserializeNonEmpty = runStateT (deserialize @BitMap) [66,77,80,2,2,0,1,2,3]
-- > testDeserializeNonEmpty
-- Right (BitMap {bmp = ASCII, dimensions = Dimensions {width = SPromoted (SFin @256 @('Fin 2)), height = SPromoted (SFin @256 @('Fin 2))}, pixels = PixelData {pixels = GeneralizedVector (GeneralizedVector (0 :> (1 :> Nil)) :> (GeneralizedVector (2 :> (3 :> Nil)) :> Nil))}},[])

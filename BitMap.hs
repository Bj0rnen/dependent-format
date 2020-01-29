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
import Generics.Kind.TH

import DepKDeserializeWord (Promoted, GeneralizedVector(..), sWord8)
import ASCII (ASCII(..))
import Data.Word (Word8)
import Data.Singletons.Fin (Sing)
import Vector (Vector(..))
import Control.Monad.State (StateT(..))

data BitMap = forall (width :: Promoted Word8) (height :: Promoted Word8). BitMap
    { bmp    :: ASCII "BMP"
    , width  :: Sing width
    , height :: Sing height
    , pixels :: GeneralizedVector (GeneralizedVector Word8 width) height
    }
deriving instance Show BitMap
$(deriveGenericK ''BitMap)
deriving instance DepKDeserialize BitMap

testSerializeEmpty :: [Word8]
testSerializeEmpty = serialize (BitMap
    { bmp = ASCII
    , width = sWord8 @0
    , height = sWord8 @0
    , pixels = GeneralizedVector Nil
    })

testDeserializeEmpty :: Either DeserializeError (BitMap, [Word8])
testDeserializeEmpty = runStateT (deserialize @BitMap) [66,77,80,0,0]

testSerializeNonEmpty :: [Word8]
testSerializeNonEmpty = serialize (BitMap
    { bmp = ASCII
    , width = sWord8 @2
    , height = sWord8 @2
    , pixels = GeneralizedVector (GeneralizedVector (0 :> 1 :> Nil) :> GeneralizedVector (2 :> 3 :> Nil) :> Nil)
    })

testDeserializeNonEmpty :: Either DeserializeError (BitMap, [Word8])
testDeserializeNonEmpty = runStateT (deserialize @BitMap) [66,77,80,2,2,0,1,2,3]

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType #-}

module ASCII where

import DepKDeserialize
import Generics.Kind
--import Generics.Kind.TH

import GHC.TypeLits
import Data.Proxy
import Data.Char
import Data.Word
import Data.Kind
import Control.Monad.State
import Control.Monad.Except

data ASCII (s :: Symbol) = ASCII
    deriving (Show)

ascii :: String -> [Word8]
ascii str =
    if not (all isAscii str) then
        error "Not an ASCII string"
    else
        map (fromIntegral @_ @Word8 . ord) str

instance KnownSymbol s => DepKDeserialize (ASCII s) where
    type SerConstraints (ASCII s) _ = ()
    type Require (ASCII s) as ds = ()
    type Learn (ASCII s) _ ds = ds
    depKSerialize _ (TheseK Proxy v) =
        let str = symbolVal (Proxy @s)
        in  ascii str
    depKDeserialize _ = do
        let str = symbolVal (Proxy @s)
            expectedBytes = ascii str
        withoutKnowledge $ expectBytes expectedBytes
        return (AnyK (Proxy @'LoT0) ASCII)

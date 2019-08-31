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

module Serialize where

import Vector

import Data.Kind
import GHC.TypeNats
import Data.Kind.Fin
import Data.Singletons
import Data.Singletons.TypeLits
import Data.Singletons.Fin
import Exinst

import Data.Constraint

import Data.Word
import Data.Bits
import Numeric.Natural

class Serialize a where
    serialize :: a -> [Word8]
    deserialize :: [Word8] -> (a, [Word8])

instance Serialize Word8 where
    serialize a = [a]
    deserialize (b : bs) = (b, bs)

instance Serialize Word16 where
    serialize a =
        [ fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    deserialize bs =
        case deserialize bs of
            (a :> b :> Nil :: Vector Word8 2, bs') ->
                (       (fromIntegral a) `shiftL` 8
                    .|. fromIntegral b
                , bs'
                )

instance Serialize Word32 where
    serialize a =
        [ fromIntegral ((a `shiftR` 24) .&. 0xFF)
        , fromIntegral ((a `shiftR` 16) .&. 0xFF)
        , fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    deserialize bs =
        case deserialize bs of
            (a :> b :> c :> d :> Nil :: Vector Word8 4, bs') ->
                (       (fromIntegral a) `shiftL` 24
                    .|. (fromIntegral b) `shiftL` 16
                    .|. (fromIntegral c) `shiftL` 8
                    .|. fromIntegral d
                , bs'
                )

instance Serialize Word64 where
    serialize a =
        [ fromIntegral ((a `shiftR` 56) .&. 0xFF)
        , fromIntegral ((a `shiftR` 48) .&. 0xFF)
        , fromIntegral ((a `shiftR` 40) .&. 0xFF)
        , fromIntegral ((a `shiftR` 32) .&. 0xFF)
        , fromIntegral ((a `shiftR` 24) .&. 0xFF)
        , fromIntegral ((a `shiftR` 16) .&. 0xFF)
        , fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    deserialize bs =
        case deserialize bs of
            (a :> b :> c :> d :> e :> f :> g :> h :> Nil :: Vector Word8 8, bs') ->
                (       (fromIntegral a) `shiftL` 56
                    .|. (fromIntegral b) `shiftL` 48
                    .|. (fromIntegral c) `shiftL` 40
                    .|. (fromIntegral d) `shiftL` 32
                    .|. (fromIntegral e) `shiftL` 24
                    .|. (fromIntegral f) `shiftL` 16
                    .|. (fromIntegral g) `shiftL` 8
                    .|. fromIntegral h
                , bs'
                )

instance Serialize Natural where  -- 8-bit
    serialize n = [fromIntegral n]
    deserialize bs =
        case deserialize bs of
            (a :: Word8, bs') ->
                (fromIntegral a, bs')

instance SingI n => Serialize (Sing (n :: Nat)) where  -- 8-bit
    serialize SNat = serialize $ natVal @n Proxy
    deserialize bs =
        withKnownNat @n sing $
            case deserialize bs of
                (n :: Natural, bs') ->
                    if n == natVal @n Proxy then
                        (SNat , bs')
                    else
                        error "Deserialized wrong SNat"

instance (SingKind t, Serialize (Demote t)) => Serialize (Some1 (Sing :: t -> Type)) where
    serialize (Some1 s1 s2) = serialize (FromSing s2)
    deserialize bs =
        case deserialize bs of
            (FromSing s, bs') -> (Some1 s s, bs')

instance SingI a => Serialize (Sing (a :: Fin n)) where  -- 8-bit
    serialize SFin = [fromIntegral $ finVal @a]
    deserialize (a : bs) =
        withKnownFin @a sing $
            if fromIntegral a == finVal @a then
                (SFin, bs)
            else
                error "Deserialized wrong SNat"

instance (Serialize a, SingI n) => Serialize (Vector a n) where
    serialize (v :: Vector a n) =
        withKnownNat @n sing $
            Vector.ifZeroElse @n [] $ \_ ->
                case v of
                    x :> xs ->
                        serialize x ++ serialize xs \\ samePredecessor @n
    deserialize bs =
        withKnownNat @n sing $
            Vector.ifZeroElse @n (Nil, bs) $ \(Proxy :: Proxy n1) ->
                case deserialize @a bs of
                    (a, bs') ->
                        case deserialize @(Vector a n1) bs' of
                            (as, bs'') -> (a :> as, bs'')


--instance SingI n => Serialize (SomeSing (Fin n)) where
--    serialize (SomeSing (SFin :: Sing a)) = serialize (SFin @n @a)
--    deserialize bs =
--        case deserialize bs of
--            (n :: Word8, bs') ->
--                case sing @n of
--                    SNat ->
--                        case someFinVal (fromIntegral n) of
--                            Nothing -> error $ show n ++ " out of bounds for Fin"  -- TODO: Not like this!
--                            Just (SomeFin (Proxy :: Proxy a)) ->
--                                (SomeSing @(Fin n) @a SFin, bs')
--instance Serialize (Fin n) where
--    serialize a = undefined
--    deserialize bs = undefined
--data IndexedOnFin256 (size :: Fin 256) = IndexedOnWord8
--    { x :: Sing size
--    --, arr :: Vector Word8 size
--    } deriving (GHC.Generic1, Show, HasDepLevel, Serialize)
--
--diow8 :: Some1 IndexedOnFin256
--diow8 = fst $ deserializeSome1 [1]
--siow8 :: [Word8]
--siow8 = serializeSome1 diow8

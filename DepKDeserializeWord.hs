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

module DepKDeserializeWord where

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
import Control.Monad.Except


-- NOTE: I don't love the repetitiveness of the type family approach below.
--  I tried a data family like in this comment, but apparently data family instance
--  constructors simply never promote to the kind level... GHC's user guide says it
--  would require full dependent types. I'm not sure why.
--data family Promote (a :: Type)
--
--newtype instance Promote Word8 = PWord8 (Fin 256)
--newtype instance Promote Word16 = PWord16 (Fin 65536)
--newtype instance Promote Word32 = PWord32 (Fin 4294967296)
--newtype instance Promote Word64 = PWord64 (Fin 18446744073709551616)

newtype PWord8 = PWord8 (Fin 256)
newtype PWord16 = PWord16 (Fin 65536)
newtype PWord32 = PWord32 (Fin 4294967296)
newtype PWord64 = PWord64 (Fin 18446744073709551616)

-- NOTE: Also, it turns out that there are no uses for this type family either.
--  Basically it seems I have to use concrete stand-alone types like PWord8 directly.
--  I could use types like Fin 256 directly too and say Demote (Fin 256) = Word8,
--  but I find that a somewhat arbitrary mapping, hence these newtype wrappers.
--type family Promote (a :: Type) = (b :: Type) | b -> a
--
--type instance Promote Word8 = PWord8
--type instance Promote Word16 = PWord16
--type instance Promote Word32 = PWord32
--type instance Promote Word64 = PWord64
--
-- TODO: Potentially, we can explore other approaches than the `Sing (a :: Promote Word8)`
--  that I had imagined, by not trying to make something that can be wrapped in a sing.
--  For example, what if instead of `Sing (a :: Promote Word8)`, we try to make
--  something like `PromotedSing (a :: Word8)` work?

data instance Sing :: PWord8 -> Type where
    SWord8 :: forall (a :: Fin 256). Sing a -> Sing ('PWord8 a)
data instance Sing :: PWord16 -> Type where
    SWord16 :: forall (a :: Fin 65536). Sing a -> Sing ('PWord16 a)
data instance Sing :: PWord32 -> Type where
    SWord32 :: forall (a :: Fin 4294967296). Sing a -> Sing ('PWord32 a)
data instance Sing :: PWord64 -> Type where
    SWord64 :: forall (a :: Fin 18446744073709551616). Sing a -> Sing ('PWord64 a)

instance Show (Sing (a :: PWord8)) where
    show (SWord8 a) = "SWord8 (" ++ show a ++ ")" -- TODO: Not a proper implementation...
instance Show (Sing (a :: PWord16)) where
    show (SWord16 a) = "SWord16 (" ++ show a ++ ")" -- TODO: Not a proper implementation...
instance Show (Sing (a :: PWord32)) where
    show (SWord32 a) = "SWord32 (" ++ show a ++ ")" -- TODO: Not a proper implementation...
instance Show (Sing (a :: PWord64)) where
    show (SWord64 a) = "SWord64 (" ++ show a ++ ")" -- TODO: Not a proper implementation...

instance SingKind (PWord8) where
    type Demote (PWord8) = Word8
    fromSing (SWord8 (SFin :: Sing a)) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for PWord8. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SWord8 (SFin :: Sing a))

instance SingKind (PWord16) where
    type Demote (PWord16) = Word16
    fromSing (SWord16 (SFin :: Sing a)) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for PWord16. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SWord16 (SFin :: Sing a))

instance SingKind (PWord32) where
    type Demote (PWord32) = Word32
    fromSing (SWord32 (SFin :: Sing a)) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin SWord32. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SWord32 (SFin :: Sing a))

instance SingKind (PWord64) where
    type Demote (PWord64) = Word64
    fromSing (SWord64 (SFin :: Sing a)) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin SWord64. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SWord64 (SFin :: Sing a))


-- TODO: Too specialized? Not sure what's a good abstraction yet. Could be an x-to-y (i.e. PWord8-to-Nat) conversion.
--  Or it could be more semantics/purpose focused, like "Can this kind represent a vector's (or other collection's) length?".
--  In this form it's basically "Can this kind losslessly and unambiguously be converted to a natural number?".
class HasToNat k where
    type ToNat (a :: k) :: Nat
    toNat :: Sing (a :: k) -> Sing (ToNat a :: Nat)
instance HasToNat PWord8 where
    type ToNat ('PWord8 a) = FinToNat a
    toNat (SWord8 (SFin :: Sing a)) = withDict (knownFinToKnownNat @a Dict) SNat
instance HasToNat PWord16 where
    type ToNat ('PWord16 a) = FinToNat a
    toNat (SWord16 (SFin :: Sing a)) = withDict (knownFinToKnownNat @a Dict) SNat
instance HasToNat PWord32 where
    type ToNat ('PWord32 a) = FinToNat a
    toNat (SWord32 (SFin :: Sing a)) = withDict (knownFinToKnownNat @a Dict) SNat
instance HasToNat PWord64 where
    type ToNat ('PWord64 a) = FinToNat a
    toNat (SWord64 (SFin :: Sing a)) = withDict (knownFinToKnownNat @a Dict) SNat

-- TODO: Is there room for more generalization? A "Generalized" anything that's indexed by a Nat?
--  A "Generalized" anything that's indexed by anything that can by converted to whatever the wrapped thing is indexed by?
--  Also, this case is quite simple because deserializing a Vector doesn't learn anything. Generalizing something like Sing
--  would require conversion in the opposite direction, which, unless the kinds are bijective, one direction would have to
--  to be partial...
--  Not to mention generalizing things that are indexed on more than one type variable, e.g. the L0R1 example type.
newtype GeneralizedVector (a :: Type) (n :: k) where
    GeneralizedVector :: forall a k (n :: k). Vector a (ToNat n) -> GeneralizedVector a n
deriving instance Show (Vector a (ToNat n)) => Show (GeneralizedVector a n)

instance (Serialize a, HasToNat k) => DepKDeserialize (GeneralizedVector a :: k -> Type) where
    type Require (GeneralizedVector a :: k -> Type) as ds = RequireAtom (AtomAt 'VZ as) ds
    type Learn (GeneralizedVector a :: k -> Type) as ds = ds

    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (k -> Type))
        .  Require (GeneralizedVector a) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK (GeneralizedVector a), KnowledgeList (Learn (GeneralizedVector a) as ds))
    depKDeserialize _ kl = do
        case getAtom @d @k @(AtomAt 'VZ as) @ds kl of
            SomeSing (n :: Sing n) ->
                case toNat n of
                    (SNat :: Sing (ToNat n)) -> do
                        a <- deserialize @(Vector a (ToNat n))
                        return (AnyK (Proxy @(n :&&: 'LoT0)) (GeneralizedVector a), kl)

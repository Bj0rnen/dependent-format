{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module DepKDeserializeWord where

import DepKDeserialize
import DepKDeserializeLet
import Vector

import Data.Singletons.TH
import GHC.TypeNats
import Data.Singletons.TypeLits
import Data.Kind

import           Generics.Kind hiding (Nat, (:~:))
import Generics.Kind.TH

import Data.Constraint
import Data.Constraint.Nat

import Data.Word
import Data.Int
import Data.Singletons.Fin
import Data.Singletons.FinInt

import Control.Monad.Indexed


type family Promote (a :: Type) = (b :: Type) | b -> a
newtype Promoted (a :: Type) where
    Promoted :: forall a. Promote a -> Promoted a
deriving instance Show (Promote a) => Show (Promoted a)
data instance Sing :: Promoted a -> Type where
    SPromoted :: Sing (x :: Promote a) -> Sing ('Promoted x :: Promoted a)
instance SingI x => SingI ('Promoted x :: Promoted a) where
    sing = SPromoted (sing @x)
deriving instance (pa ~ Promote a, forall y. Show (Sing (y :: pa))) => Show (Sing (x :: Promoted a))

type instance Promote Word8 = Fin 256
type instance Promote Word16 = Fin 65536
type instance Promote Word32 = Fin 4294967296
type instance Promote Word64 = Fin 18446744073709551616


instance SingKind (Promoted Word8) where
    type Demote (Promoted Word8) = Word8
    fromSing (SPromoted s) = fromIntegral $ sFinVal s
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Word8. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SPromoted (SFin :: Sing a))

instance SingKind (Promoted Word16) where
    type Demote (Promoted Word16) = Word16
    fromSing (SPromoted s) = fromIntegral $ sFinVal s
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Word16. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SPromoted (SFin :: Sing a))

instance SingKind (Promoted Word32) where
    type Demote (Promoted Word32) = Word32
    fromSing (SPromoted s) = fromIntegral $ sFinVal s
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Word32. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SPromoted (SFin :: Sing a))

instance SingKind (Promoted Word64) where
    type Demote (Promoted Word64) = Word64
    fromSing (SPromoted s) = fromIntegral $ sFinVal s
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Word64. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SPromoted (SFin :: Sing a))


-- TODO: Too specialized? Not sure what's a good abstraction yet. Could be an x-to-y (i.e. Promoted Word8-to-Nat) conversion.
--  Or it could be more semantics/purpose focused, like "Can this kind represent a vector's (or other collection's) length?".
--  In this form it's basically "Can this kind losslessly and unambiguously be converted to a natural number?".
class HasToNat k where
    type ToNat (a :: k) :: Nat
    toNat :: Sing (a :: k) -> Sing (ToNat a :: Nat)
instance HasToNat (Promoted Word8) where
    type ToNat ('Promoted n) = FinToNat n
    toNat (SPromoted s) = sFinToSNat s
instance HasToNat (Promoted Word16) where
    type ToNat ('Promoted n) = FinToNat n
    toNat (SPromoted s) = sFinToSNat s
instance HasToNat (Promoted Word32) where
    type ToNat ('Promoted n) = FinToNat n
    toNat (SPromoted s) = sFinToSNat s
instance HasToNat (Promoted Word64) where
    type ToNat ('Promoted n) = FinToNat n
    toNat (SPromoted s) = sFinToSNat s


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
    -- TODO: Copy-pasted from (Vector a) instance. Prefer delegation.
    depKSerialize (AnyK (Proxy :: Proxy xs) (GeneralizedVector a)) =
        withSingI (resolveLength a) $
            depKSerialize @_ @(Vector a (ToNat (InterpretVar 'VZ xs))) (AnyK Proxy a)
        where
            resolveLength :: forall a n. Vector a n -> Sing n
            resolveLength Nil = SNat @0
            resolveLength (_ :> xs) =
                case resolveLength xs of
                    (SNat :: Sing m) -> SNat @(1 + m) \\ plusNat @1 @m
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (k -> Type))
        .  Require (GeneralizedVector a) as ds
        => Proxy as -> IxGet ds (Learn (GeneralizedVector a) as ds) (AnyK (GeneralizedVector a))
    depKDeserialize _ =
        igetAtom @d @k @(AtomAt 'VZ as) @ds >>>= \(SomeSing (n :: Sing n)) ->
        case toNat n of
            (SNat :: Sing (ToNat n)) -> AnyK (Proxy @(n :&&: 'LoT0)) <$> withoutKnowledge do
                a <- deserialize @(Vector a (ToNat n))
                return $ GeneralizedVector a


-- Using this, GeneralizedVector isn't really necessary.
data WordToNat :: a ~> Nat
type instance Apply WordToNat n = ToNat n
instance HasToNat a => SingI (WordToNat :: a ~> Nat) where
    sing = singFun1 toNat


-- Leveraging the above, we can define the equivalent of GeneralizedVector in just a few lines:
data GVector (a :: Type) (n :: k) = forall (m :: Nat). GVector
    { m :: Let WordToNat n m
    , v :: Vector a m
    }
deriving instance Show a => Show (GVector a n)
-- TODO: Should all (non-test) uses of TemplateHaskell, be avoided or moved to a *.TH module?
$(deriveGenericK ''GVector)
deriving instance (Serialize a, HasToNat k) => DepKDeserialize (GVector a :: k -> Type)


class HasIntToMaybeNat k where
    type IntToMaybeNatF (a :: k) :: Maybe Nat
    intToNat :: Sing (a :: k) -> Sing (IntToMaybeNatF a :: Maybe Nat)
type instance Promote Int8 = FinInt 128 128
instance HasIntToMaybeNat (Promoted Int8) where
    type IntToMaybeNatF ('Promoted n) = FinIntToMaybeNat n
    intToNat (SPromoted s) = sFinIntToSNat s
instance SingKind (Promoted Int8) where
    type Demote (Promoted Int8) = Int8
    fromSing (SPromoted s) = fromIntegral $ sFinIntVal s
    toSing n = case someFinIntVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Int8. This should not be possible."
        Just (SomeFinInt (_ :: Proxy a)) -> SomeSing (SPromoted (SFinInt :: Sing a))

data IntToMaybeNat :: a ~> Maybe Nat
type instance Apply IntToMaybeNat n = IntToMaybeNatF n
instance HasIntToMaybeNat a => SingI (IntToMaybeNat :: a ~> Maybe Nat) where
    sing = singFun1 intToNat

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
import Proof

import Data.Singletons.TH
import GHC.TypeNats
import Data.Singletons.TypeLits
import Data.Singletons.ShowSing
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
import Control.Monad.Indexed.State

import Unsafe.Coerce


type family Promote (a :: Type) = (b :: Type) | b -> a
newtype Promoted (a :: Type) where
    Promoted :: forall a. Promote a -> Promoted a
deriving instance Show (Promote a) => Show (Promoted a)
data SPromoted :: Promoted a -> Type where
    SPromoted :: Sing (x :: Promote a) -> SPromoted ('Promoted x :: Promoted a)
type instance Sing = SPromoted
instance SingI x => SingI ('Promoted x :: Promoted a) where
    sing = SPromoted (sing @x)
deriving instance (pa ~ Promote a, forall (y :: pa) sing. sing ~ Sing => Show (sing y)) => Show (SPromoted (x :: Promoted a))

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

sWord8 :: forall n. (KnownNat n, CmpNat n 256 ~ 'LT) => Sing ('Promoted ('Fin n) :: Promoted Word8)
sWord8 = SPromoted (SFin @256 @('Fin n))
sWord16 :: forall n. (KnownNat n, CmpNat n 65536 ~ 'LT) => Sing ('Promoted ('Fin n) :: Promoted Word16)
sWord16 = SPromoted (SFin @65536 @('Fin n))
sWord32 :: forall n. (KnownNat n, CmpNat n 4294967296 ~ 'LT) => Sing ('Promoted ('Fin n) :: Promoted Word32)
sWord32 = SPromoted (SFin @4294967296 @('Fin n))
sWord64 :: forall n. (KnownNat n, CmpNat n 18446744073709551616 ~ 'LT) => Sing ('Promoted ('Fin n) :: Promoted Word64)
sWord64 = SPromoted (SFin @18446744073709551616 @('Fin n))

-- TODO: Too specialized? Not sure what's a good abstraction yet. Could be an x-to-y (i.e. Promoted Word8-to-Nat) conversion.
--  Or it could be more semantics/purpose focused, like "Can this kind represent a vector's (or other collection's) length?".
--  In this form it's basically "Can this kind losslessly and unambiguously be converted to a natural number?".
class HasToNat k where
    type ToNat (a :: k) :: Nat
    toNat :: Sing (a :: k) -> Sing (ToNat a :: Nat)
instance HasToNat Nat where
    type ToNat n = n
    toNat s = s
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

instance HasToNat k => DepKDeserialize (GeneralizedVector :: Type -> k -> Type) where
    type Require (GeneralizedVector :: Type -> k -> Type) as ds =
        ( DepKDeserialize (AtomKonConstructor (AtomAt 'VZ as))
        , Require (AtomKonConstructor (AtomAt 'VZ as)) (AtomKonAtomList (AtomAt 'VZ as)) ds
        , RequireAtom (AtomAt ('VS 'VZ) as) ds
        -- Saying that we don't learn from the elements might turn out to be overly strict.
        -- It wouldn't be hard to instead claim inside the methods that there's no harm in that.
        , Learn (AtomKonConstructor (AtomAt 'VZ as)) (AtomKonAtomList (AtomAt 'VZ as)) ds ~ ds
        )
    type Learn (GeneralizedVector :: Type -> k -> Type) as ds = ds
    depKSerialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Type -> k -> Type)) (xs :: LoT (Type -> k -> Type))
        .  Require (GeneralizedVector :: Type -> k -> Type) as ds
        => Proxy as -> TheseK (GeneralizedVector :: Type -> k -> Type) xs -> IxState (KnowledgeList ds) (KnowledgeList (Learn (GeneralizedVector :: Type -> k -> Type) as ds)) [Word8]
    depKSerialize (Proxy :: Proxy as) (TheseK (Proxy :: Proxy xs) (GeneralizedVector a)) =
        letT @(HeadLoT xs) \(Proxy :: Proxy a) ->
        iget >>>= \kl ->
        case getAtom @d @k @(AtomAt ('VS 'VZ) as) kl of
            SomeSing (n :: Sing n) ->
                case toNat n of
                    (SNat :: Sing (ToNat n)) ->
                        axm @n @(InterpretVar ('VS 'VZ) xs) $
                        depKSerialize
                            @(Type -> Nat -> Type)
                            @Vector
                            (Proxy @('AtomCons (AtomAt 'VZ as) ('AtomCons ('Kon (ToNat n)) 'AtomNil)))
                            (TheseK (Proxy @(a :&&: ToNat n :&&: 'LoT0)) a)
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Type -> k -> Type))
        .  Require (GeneralizedVector :: Type -> k -> Type) as ds
        => Proxy as -> IxGet ds (Learn (GeneralizedVector :: Type -> k -> Type) as ds) (AnyK (GeneralizedVector :: Type -> k -> Type))
    depKDeserialize (Proxy :: Proxy as) =
        igetAtom @d @k @(AtomAt ('VS 'VZ) as) @ds >>>= \(SomeSing (n :: Sing n)) ->
        case toNat n of
            (SNat :: Sing (ToNat n)) ->
                IxGet $ IxStateT $ \(kl, bs) ->
                    case runIxStateT
                            (runIxGet $
                                depKDeserialize
                                    @(Type -> Nat -> Type)
                                    @Vector
                                    (Proxy @('AtomCons (AtomAt 'VZ as) ('AtomCons ('Kon (ToNat n)) 'AtomNil))))
                            (kl, bs) of
                        Left e -> Left e
                        Right (AnyK (Proxy :: Proxy xs) a, (_, bs')) ->
                            letT @(HeadLoT xs) \(Proxy :: Proxy a) ->
                            -- TODO: We want to show (properly) that (HeadLoT xs ~ ToNat n)
                            axm @(HeadLoT (TailLoT xs)) @(ToNat n) $
                            Right (AnyK (Proxy @(a :&&: n :&&: 'LoT0)) (GeneralizedVector a), (kl, bs'))

instance HasToNat k => DepKDeserialize (GeneralizedVector a :: k -> Type) where
    type Require (GeneralizedVector a :: k -> Type) as ds = Require1Up (GeneralizedVector a :: k -> Type) as ds
    type Learn (GeneralizedVector a :: k -> Type) as ds = Learn1Up (GeneralizedVector a :: k -> Type) as ds
    depKSerialize = depKSerialize1Up
    depKDeserialize = depKDeserialize1Up

instance HasToNat k => DepKDeserialize (GeneralizedVector a (n :: k)) where
    type Require (GeneralizedVector a (n :: k)) as ds = Require1Up (GeneralizedVector a (n :: k)) as ds
    type Learn (GeneralizedVector a (n :: k)) as ds = Learn1Up (GeneralizedVector a (n :: k)) as ds
    depKSerialize = depKSerialize1Up
    depKDeserialize = depKDeserialize1Up

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
deriving instance HasToNat k => DepKDeserialize (GVector :: Type -> k -> Type)
deriving instance (Serialize a, HasToNat k) => DepKDeserialize (GVector a :: k -> Type)
deriving instance (Serialize a, HasToNat k) => DepKDeserialize (GVector a (n :: k))


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
--sInt8 :: forall n. (KnownNat n, CmpNat n 256 ~ 'LT) => Sing ('Promoted n :: Promoted Int8)
sInt8 :: forall i. KnownFinInt i => Sing ('Promoted i :: Promoted Int8)
sInt8 = SPromoted (SFinInt @128 @128 @i)

data IntToMaybeNat :: a ~> Maybe Nat
type instance Apply IntToMaybeNat n = IntToMaybeNatF n
instance HasIntToMaybeNat a => SingI (IntToMaybeNat :: a ~> Maybe Nat) where
    sing = singFun1 intToNat

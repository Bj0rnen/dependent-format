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
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}

module DependentRecord where

import Data.Singletons
import Data.Singletons.TH
import GHC.TypeNats
import Data.Singletons.TypeLits
import Data.Kind

import GHC.Generics

import Data.Proxy
import Data.Constraint
import Unsafe.Coerce
import Data.Constraint.Forall

import Data.Word
import Numeric.Natural

import Exinst

data Vector a n where
    Nil :: Vector a 0
    (:>) :: IsNonZero (1 + n) ~ 'True => a -> Vector a n -> Vector a (1 + n)  -- NOTE: The IsNonZero thing makes ifZeroElse's 0-case fail this pattern match. Hope there's some nicer way to achieve this.
deriving instance Show a => Show (Vector a n)
infixr :>

data DependentPair (size :: Nat) = DependentPair
    { size :: Sing size
    , arr :: Vector Word8 size
    } deriving (Show, Generic1)

lol :: Rep1 DependentPair 2
lol = from1 (DependentPair SNat (1 :> 2 :> Nil))

class Serialize a where
    serialize :: a -> [Word8]
    deserialize :: [Word8] -> (a, [Word8])

instance Serialize Word8 where
    serialize a = [a]
    deserialize (b : bs) = (b, bs)

instance KnownNat n => Serialize (Sing (n :: Nat)) where  -- 8-bit
    serialize SNat = [fromIntegral $ natVal @n Proxy]
    deserialize (n : bs)
        | fromIntegral n == natVal @n Proxy = (SNat, bs)
        | otherwise = error "Deserialized wrong SNat"

newtype Magic n = Magic (KnownNat n => Dict (KnownNat n))
magic :: forall n m o. (Natural -> Natural -> Natural) -> (KnownNat n, KnownNat m) :- KnownNat o
magic f = Sub $ unsafeCoerce (Magic Dict) (natVal (Proxy :: Proxy n) `f` natVal (Proxy :: Proxy m))
axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))
predecessor :: forall n n1. ((1 + n1) ~ n) :- ((n - 1) ~ n1)
predecessor = Sub axiom
plusMinusInverse :: forall n m. (n `CmpNat` (1 + m) ~ 'LT) :- ((n + (m - n)) ~ m)
plusMinusInverse = Sub axiom
unsafeSubNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n - m)
unsafeSubNat = magic (-)
type family
    IsNonZero (n :: Nat) = (nonzero :: Bool) where
    IsNonZero 0 = 'False
    IsNonZero n = 'True
ifZeroElse :: forall n r. KnownNat n => (n ~ 0 => r) -> (forall n1. (KnownNat n1, n ~ (1 + n1), IsNonZero n ~ 'True) => Proxy n1 -> r) -> r
ifZeroElse z s =
    case sameNat @n @0 Proxy Proxy of
        Just Refl -> z
        Nothing ->
            withDict (axiom :: Dict (1 `CmpNat` (1 + n) ~ 'LT)) $
                withDict (axiom :: Dict (IsNonZero n ~ 'True)) (s Proxy) \\ unsafeSubNat @n @1 \\ plusMinusInverse @1 @n
samePredecessor :: forall n n1 n2. (n ~ (1 + n1), n ~ (1 + n2)) :- (n1 ~ n2)
samePredecessor = Sub axiom
instance (Serialize a, KnownNat n) => Serialize (Vector a n) where
    serialize (v :: Vector a n) =
        ifZeroElse @n [] $ \_ ->
            case v of
                x :> xs ->
                    serialize x ++ serialize xs \\ samePredecessor @n
    deserialize bs =
        ifZeroElse @n (Nil, bs) $ \(Proxy :: Proxy n1) ->
            case deserialize @a bs of
                (a, bs') ->
                    case deserialize @(Vector a n1) bs' of
                        (as, bs'') -> (a :> as, bs'')

instance Serialize (f p) => Serialize (Rec1 f p) where
    serialize (Rec1 a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (Rec1 a, bs')

instance Serialize (f p) => Serialize (M1 i c f p) where
    serialize (M1 a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (M1 a, bs')

instance (Serialize (a p), Serialize (b p)) => Serialize ((a :*: b) p) where
    serialize (a :*: b) = serialize a ++ serialize b
    deserialize bs =
        case deserialize @(a p) bs of
            (a, bs') ->
                case deserialize @(b p) bs' of
                    (b, bs'') -> (a :*: b, bs'')


slol = serialize lol
dlol :: (Rep1 DependentPair 2, [Word8])
dlol = deserialize [2, 1, 2]

instance Serialize (SomeSing Nat) where
    serialize (SomeSing (SNat :: Sing n)) = serialize (SNat @n)
    deserialize bs =
        case deserialize bs of
            (a :: Word8, bs') ->
                case someNatVal (fromIntegral a) of
                    SomeNat (Proxy :: Proxy n) ->
                        (SomeSing @Nat @n SNat, bs')

instance Serialize (Some1 (Rec1 f)) where
    serialize (Some1 s (Rec1 a)) = undefined  --serialize a  -- TODO: ForallF? KnownImplies?
    deserialize = undefined


-- TODO: Still not sure if this can generalize to more than one "variable" with some trickery.

--type family
--    Fst p where
--    Fst '(a, _) = a
--type family
--    Snd p where
--    Snd '(_, b) = b

--data Fst (p :: (a, b)) where
--    Fst :: a -> Fst '(a, b)
--deriving instance Show a => Show (Fst '(a, b))
--data Snd (p :: (a, b)) where
--    Snd :: b -> Snd '(a, b)
--deriving instance Show b => Show (Snd '(a, b))

--data Fst (p :: (a, b)) deriving Show
--data Snd (p :: (a, b))

-- $(singletons [d|
--     data Fst (p :: (Type, Type)) where
--         Fst :: a -> Fst '(a, b)
--     |])
-- deriving instance Show a => Show (Fst '(a, b))
-- $(singletons [d|
--     data Fst (a :: Type) where
--         Fst :: (a, b) -> Fst a
--     |])
--deriving instance Show (Fst a)
--deriving instance Show (Sing ('Fst size1size2))

--data DependentMore (size1size2 :: (Nat, Nat)) = DependentMore
--    { size1 :: Sing (Fst size1size2)
--    , size2 :: Sing (Snd size1size2)
--    , arr1 :: Vector Word8 (Fst size1size2)
--    , arr2 :: Vector Word8 (Snd size1size2)
--    } deriving (Show)

--exampleDependentMore :: DependentMore '(1, 2)
--exampleDependentMore = DependentMore SNat SNat (3 :> Nil) (4 :> (5 :> Nil))

--type family Functionalize (a :: Type) :: k
--
--data Fst (p :: (a, b))
--data Snd (p :: (a, b))
--
--type instance Functionalize (Fst '(a, b)) = a
--type instance Functionalize (Snd '(a, b)) = b
--
--data SingOf (k :: Type) (a :: Type) where
--    SingOf :: Sing (Functionalize a :: k) -> SingOf k a
--deriving instance Show (Sing (Functionalize a :: k)) => Show (SingOf k a)
--instance Functor (SingOf k) where
--    fmap f (SingOf s) = SingOf (unsafeCoerce s)  -- TODO: Sure, that's going to end up well...
--
--data VectorOf (a :: Type) (n :: Type) where
--    VectorOf :: Vector a (Functionalize n) -> VectorOf a n
--    deriving Show
--instance Functor (VectorOf a) where
--    fmap f (VectorOf v) = VectorOf (unsafeCoerce v)  -- TODO: Sure, that's going to end up well...
--
--data DependentMore (size1size2 :: (Nat, Nat)) = DependentMore
--    { size1 :: SingOf Nat (Fst size1size2)
--    , size2 :: SingOf Nat (Snd size1size2)
--    , arr1 :: VectorOf Word8 (Fst size1size2)
--    , arr2 :: VectorOf Word8 (Snd size1size2)
--    } deriving (Show, Generic1)
--
--exampleDependentMore :: DependentMore '(1, 2)
--exampleDependentMore = DependentMore (SingOf SNat) (SingOf SNat) (VectorOf (3 :> Nil)) (VectorOf (4 :> 5 :> Nil))

--type family Fst (a :: Type) :: Type
--type instance Fst (Sing ('(a, b) :: (Nat, Nat))) = Sing a

--data family Fst (p :: (k1, k2)) (a :: k)
--data instance Fst '(a, b) Sing where
--    FstSing :: Sing a -> Fst '(a, b) Sing
----instance Functor Fst
--data instance Fst '(n, m) (Vector a) where
--    FstVector :: Vector a n -> Fst '(n, m) (Vector a)

data Fst (f :: k -> Type) (p :: (k, k2)) where
    Fst :: f a -> Fst f '(a, b)
instance ForallF Show f => Show (Fst f p) where
    show (Fst (a :: f a)) = "Fst (" ++ (show a \\ instF @Show @f @a) ++ ")"

data Snd (f :: k -> Type) (p :: (k1, k)) where
    Snd :: f b -> Snd f '(a, b)
instance ForallF Show f => Show (Snd f p) where
    show (Snd (a :: f b)) = "Snd (" ++ (show a \\ instF @Show @f @b) ++ ")"


--data family Snd a
--data instance Snd (Sing ('(a, b) :: (Nat, Nat))) where
--    SndSing :: Sing b -> Snd (Sing ('(a, b) :: (Nat, Nat)))
--instance Functor Snd

--type family Id (a :: Type) :: Type
--type instance Id a = a
--
--type Id (a :: Type) = a
--
--type family Applied (f :: k -> Type) (a :: k) :: Type
--type instance Applied f a = f a
--
--data DependentMore (size1size2 :: (Nat)) = DependentMore
--    { size1 :: Applied Sing size1size2
--    --, size2 :: Sing size1size2
--    --, arr1 :: Vector Word8 size1size2
--    --, arr2 :: Vector Word8 size1size2
--    } deriving (Show, Generic1)

data DependentMore (size1size2 :: (Nat, Nat)) = DependentMore
    { size1 :: Fst Sing size1size2
    , size2 :: Snd Sing size1size2
    , arr1 :: Fst (Vector Word8) size1size2
    , arr2 :: Snd (Vector Word8) size1size2
    } deriving (Show, Generic1)

exampleDependentMore :: DependentMore '(1, 2)
exampleDependentMore = DependentMore (Fst SNat) (Snd SNat) (Fst (3 :> Nil)) (Snd (4 :> 5 :> Nil))

-- TODO: The above is seemingly the best I can get with Generic1.
-- TODO: I should look back to the ideas I had some time ago where instead of relying on Generic1 (and the Generic2... that I wish existed),
-- TODO: I rely only on Generic. Then I inject distinct values on each type variable (or element of HList/tuple) as "tags" for a TaggedHList
-- TODO: I'm simply wondering if that approach is more or less a hand-baked GenericN? That would honestly be blog post worthy...

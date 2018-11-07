-- GHC 8.6.2, Singletons 2.5

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}

module ReifyImplications where

import Data.Kind
import GHC.TypeNats
import Data.Singletons
import Data.Singletons.TypeLits
import Data.Type.Equality

data EmptyVec :: Nat -> Type where
    EmptyVec :: EmptyVec 0

instance KnownNat n => Read (EmptyVec n) where
    readsPrec _ "EmptyVec" =
        case sameNat @n @0 Proxy Proxy of
            Just Refl -> [(EmptyVec, "")]
            Nothing -> []

data Some1 :: (k -> Type) -> Type where
    Some1 :: Sing a -> f a -> Some1 f

readKnowingTypeIndex ::
    forall k (f :: k -> Type). (forall x. SingI x => Read (f x)) =>
        SomeSing k -> String -> Some1 f
readKnowingTypeIndex (SomeSing s) str =
    Some1 s $ withSingI s $ read str

readKnowingNat ::
    forall (f :: Nat -> Type). (forall n. KnownNat n => Read (f n)) =>
        SomeSing Nat -> String -> Some1 f
readKnowingNat (SomeSing (SNat :: Sing a)) str =
    Some1 (SNat @a) $ read str              -- Can't write this in terms of readKnowingTypeIndex?

ev :: SomeSing Nat -> Some1 EmptyVec
--ev s = readKnowingTypeIndex s "EmptyVec"  -- Could not deduce (KnownNat x).
--ev s = readKnowingNat s "EmptyVec"        -- OK, but this doesn't work on every kind. Only Nat.

singIImpliesKnownNat :: forall r. ((forall n. SingI n => KnownNat n) => r) -> r
singIImpliesKnownNat a = undefined          -- Can't implement this?

ev s =
    singIImpliesKnownNat $
        readKnowingTypeIndex s "EmptyVec"   -- OK, if singIImpliesKnownNat was real.


-- Now, this is easy to implement. But it's not practically usable in the definition of `ev`.
data Dict :: Constraint -> Type where
    Dict :: c => Dict c

singIToKnownNat :: forall n. SingI n => Dict (KnownNat n)
singIToKnownNat = case sing @n of SNat -> Dict

-- Bonus: readKnowingNat written in terms of readKnowingTypeIndex
readKnowingNat' ::
    forall (f :: Nat -> Type). (forall n. KnownNat n => Read (f n)) =>
        SomeSing Nat -> String -> Some1 f
readKnowingNat' s str =
    singIImpliesKnownNat $
        readKnowingTypeIndex s str

{-
ev :: SomeSing Nat -> Some1 EmptyVec
ev s =
    suppose forall (n :: Nat). SingI n =>
        singIToKnownNat @n
    in
        readKnowingTypeIndex s "EmptyVec"

ev :: SomeSing Nat -> Some1 EmptyVec
ev s =
    suppose forall (n :: Nat). SingI n =>
        sing @n
    in
        readKnowingTypeIndex s "EmptyVec"

suppose1 :: forall a b r. (forall x. a x => Dict (b x)) -> ((forall x. a x => b x) => r) -> r
suppose1 Dict a = a
-}

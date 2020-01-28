{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Vector where

import Data.Kind
import GHC.TypeNats
import Numeric.Natural
import Data.Proxy
import Data.Constraint
import Data.Type.Equality

import Unsafe.Coerce


newtype Magic n = Magic (KnownNat n => Dict (KnownNat n))
magic :: forall n m o. (Natural -> Natural -> Natural) -> (KnownNat n, KnownNat m) :- KnownNat o
magic f = Sub $ unsafeCoerce (Magic Dict) (natVal (Proxy :: Proxy n) `f` natVal (Proxy :: Proxy m))
axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))
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
addNonZero :: forall n m. (IsNonZero n ~ 'True) :- (CmpNat m (m + n) ~ 'LT)
addNonZero = Sub axiom

data Vector :: Type -> Nat -> Type where
    Nil :: Vector a 0
    -- TODO: Removed the constraint below beacuse it gave me headaches, but it's probably better if I bring it back.
    (:>) :: {- IsNonZero (1 + n) ~ 'True => -} a -> Vector a n -> Vector a (1 + n)  -- NOTE: The IsNonZero thing makes ifZeroElse's 0-case fail this pattern match. Hope there's some nicer way to achieve this.
deriving instance Show a => Show (Vector a n)
infixr :>

matchVector
    :: forall a n r
    .  KnownNat n
    => Vector a n
    -> (n ~ 0 => r)
    -> (forall n1. (KnownNat n1, n ~ (1 + n1), IsNonZero n ~ 'True) => a -> Vector a n1 -> r)
    -> r
matchVector Nil z _ = z
matchVector (x :> (xs :: Vector a n1)) _ s =
    withDict (axiom :: Dict (1 `CmpNat` (1 + n) ~ 'LT)) $
        withDict (axiom :: Dict (IsNonZero n ~ 'True)) $
            s x xs
            \\ samePredecessor @n @(n - 1) @n1
            \\ unsafeSubNat @n @1
            \\ plusMinusInverse @1 @n

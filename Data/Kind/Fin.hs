{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

module Data.Kind.Fin (Fin(..), KnownFin, finVal, SomeFin(..),
                      someFinVal, someFin, sameFin,
                      FinToNat, knownFinToKnownNat,
                      ifZeroElse, ltNat, predecessor, subNat) where

import Data.Proxy
import Data.Type.Equality
import GHC.TypeNats
import Numeric.Natural
import Data.Constraint

import Unsafe.Coerce

import Control.Monad
import Text.Read
import GHC.Show (appPrec, appPrec1)


newtype Magic n = Magic (KnownNat n => Dict (KnownNat n))

magic :: forall n m o. (Natural -> Natural -> Natural) -> (KnownNat n, KnownNat m) :- KnownNat o
magic f = Sub $ unsafeCoerce (Magic Dict) (natVal (Proxy :: Proxy n) `f` natVal (Proxy :: Proxy m))

axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))

--type family S (n :: Nat) = (sn :: Nat) | sn -> n where
--    S n = (1 + n)

plusMinusInverse3'' :: forall n m. (n `CmpNat` (1 + m) ~ 'LT) :- ((n + (m - n)) ~ m)
plusMinusInverse3'' = Sub axiom

unsafeSubNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n - m)
unsafeSubNat = magic (-)

subNat :: forall n m. m `CmpNat` (1 + n) ~ 'LT => (KnownNat n, KnownNat m) :- KnownNat (n - m)
subNat = unsafeSubNat

predecessor :: forall n n1. ((1 + n1) ~ n) :- ((n - 1) ~ n1)
predecessor = Sub axiom



ifZeroElse :: forall n r. KnownNat n => (n ~ 0 => r) -> (forall n1. (KnownNat n1, n ~ (1 + n1)) => Proxy n1 -> r) -> r
ifZeroElse z s =
    case sameNat @n @0 Proxy Proxy of
        Just Refl -> z
        Nothing ->
            withDict (axiom :: Dict (1 `CmpNat` (1 + n) ~ 'LT)) $
                s Proxy \\ subNat @n @1 \\ plusMinusInverse3'' @1 @n

ltNat :: forall n m r. (KnownNat n, KnownNat m) => Maybe (n `CmpNat` m :~: 'LT)
ltNat =
    if natVal @n Proxy < natVal @m Proxy then
        Just (withDict (axiom @(n `CmpNat` m) @'LT) Refl)
    else
        Nothing


newtype MagicNat r = MagicNat (forall (n :: Nat). KnownNat n => Proxy n -> r)

reifyNat :: forall r. Natural -> (forall (n :: Nat). KnownNat n => Proxy n -> r) -> r
reifyNat n k = unsafeCoerce (MagicNat k :: MagicNat r) n Proxy






data Fin (n :: Nat) = Fin Nat
class KnownFin (a :: Fin n) where
-- <private>
    finSing :: SFin a

newtype SFin (a :: Fin n) = SFin Natural

newtype MagicFin n r = MagicFin (forall (a :: Fin n). KnownFin a => Proxy a -> r)

reifyFin :: forall n r. Natural -> (forall (a :: Fin n). KnownFin a => Proxy a -> r) -> r
reifyFin n k = unsafeCoerce (MagicFin k :: MagicFin n r) n Proxy

unsafeSomeFinVal :: forall n. Natural -> SomeFin n
unsafeSomeFinVal n = reifyFin n (\(p :: Proxy (a :: Fin n)) -> SomeFin @n @a p)
-- </private>

instance (KnownNat a, a `CmpNat` n ~ 'LT) => KnownFin ('Fin a :: Fin n) where
    finSing = SFin $ natVal @a Proxy

finVal :: forall a. KnownFin a => Natural
finVal =
    case finSing @_ @a of
        SFin x -> x

data SomeFin n where
    SomeFin :: forall n a. KnownFin (a :: Fin n) => Proxy a -> SomeFin n
instance KnownNat n => Show (SomeFin n) where
    showsPrec p (SomeFin (_ :: Proxy a)) =
        showParen (p > appPrec) $
            showString "someFin @" .
            showsPrec appPrec1 (natVal @n Proxy) .
            showString " @" .
            showsPrec appPrec1 (finVal @a)
instance KnownNat n => Read (SomeFin n) where
    readPrec = parens $ do
        Ident "someFin" <- lexP
        Punc "@" <- lexP
        n <- prec appPrec1 $ readPrec @Natural
        guard $ n == natVal @n Proxy
        Punc "@" <- lexP
        a <- prec appPrec1 $ readPrec @Natural
        msum $ return <$> someFinVal @n a


someFinVal :: forall n. KnownNat n => Natural -> Maybe (SomeFin n)
someFinVal a =
    if a < natVal @n Proxy then
        Just $ unsafeSomeFinVal a
    else
        Nothing

someFin :: forall n a. (KnownNat n, KnownNat a, a `CmpNat` n ~ 'LT) => SomeFin n
someFin = SomeFin @n @('Fin a) Proxy

sameFin :: forall n (a :: Fin n) (b :: Fin n). (KnownFin a, KnownFin b) => Maybe (a :~: b)
sameFin =
    case (finSing @n @a, finSing @n @b) of
        (SFin a, SFin b) ->
            if a == b then
                Just (unsafeCoerce Refl)
            else
                Nothing

type family
    FinToNat (a :: Fin n) :: Nat where
    FinToNat ('Fin a) = a

knownFinToKnownNat :: forall a. Dict (KnownFin a) -> Dict (KnownNat (FinToNat a))
knownFinToKnownNat Dict =
    reifyNat (finVal @a) $ \(Proxy :: Proxy n) ->
        case axiom @n @(FinToNat a) of
            Dict -> Dict

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Kind.FinInt (FinInt(..), KnownFinInt, finIntVal, SomeFinInt(..),
                         someFinIntVal, someFinInt, someFinIntNegative, someFinIntNonNegative, sameFinInt,
                         FinIntToMaybeNat) where

import Prelude hiding (Int)

import Data.Proxy
import Data.Type.Equality
import GHC.TypeNats
import Numeric.Natural

import Unsafe.Coerce

import Control.Monad
import Text.Read

import GHC.TypeLits (TypeError, ErrorMessage(..))
import Data.Constraint


data FinInt (n :: Nat) (m :: Nat) = Negative Nat | NonNegative Nat
class KnownFinInt (a :: FinInt n m) where
-- <private>
    finIntSing :: SFinInt a

newtype SFinInt (a :: FinInt n m) = SFinInt Integer

newtype MagicFinInt n m r = MagicFinInt (forall (a :: FinInt n m). KnownFinInt a => Proxy a -> r)

reifyFinInt :: forall n m r. Integer -> (forall (a :: FinInt n m). KnownFinInt a => Proxy a -> r) -> r
reifyFinInt n k = unsafeCoerce (MagicFinInt k :: MagicFinInt n m r) n Proxy

unsafeSomeFinIntVal :: forall n m. Integer -> SomeFinInt n m
unsafeSomeFinIntVal n = reifyFinInt n (\(p :: Proxy (a :: FinInt n m)) -> SomeFinInt @n @m @a p)
-- </private>

instance (KnownNat a, a `CmpNat` (n + 1) ~ 'LT, a `CmpNat` 0 ~ 'GT) => KnownFinInt ('Negative a :: FinInt n m) where
    finIntSing = SFinInt $ negate $ fromIntegral $ natVal @a Proxy
instance (KnownNat a, a `CmpNat` m ~ 'LT) => KnownFinInt ('NonNegative a :: FinInt n m) where
    finIntSing = SFinInt $ fromIntegral $ natVal @a Proxy

finIntVal :: forall a. KnownFinInt a => Integer
finIntVal =
    case finIntSing @_ @_ @a of
        SFinInt x -> x

data SomeFinInt n m where
    SomeFinInt :: forall n m a. KnownFinInt (a :: FinInt n m) => Proxy a -> SomeFinInt n m
instance (KnownNat n, KnownNat m) => Show (SomeFinInt n m) where
    showsPrec p (SomeFinInt (_ :: Proxy a)) =
        showParen (p > app_prec) $
            showString "fromJust " .
            showParen True (
                showString "someFinIntVal @" .
                showsPrec (app_prec + 1) (natVal @n Proxy) .
                showString " @" .
                showsPrec (app_prec + 1) (natVal @m Proxy) .
                showString " " .
                showsPrec (app_prec + 1) (finIntVal @a))
        where app_prec = 10
instance (KnownNat n, KnownNat m) => Read (SomeFinInt n m) where
    readPrec = parens $ do
        Ident "fromJust" <- lexP
        parens $ do
            Ident "someFinIntVal" <- lexP
            parseValue +++ do
                Punc "@" <- lexP
                n <- prec (app_prec + 1) $ readPrec @Natural
                guard $ n == natVal @n Proxy
                parseValue +++ do
                    Punc "@" <- lexP
                    m <- prec (app_prec + 1) $ readPrec @Natural
                    guard $ m == natVal @m Proxy
                    parseValue
        where
            parseValue = do
                a <- prec (app_prec + 1) $ readPrec @Integer
                msum $ fmap return $ someFinIntVal @n @m a
            app_prec = 10

someFinIntVal :: forall n m. (KnownNat n, KnownNat m) => Integer -> Maybe (SomeFinInt n m)
someFinIntVal a =
    if a >= negate (fromIntegral (natVal @n Proxy)) && a < fromIntegral (natVal @m Proxy) then
        Just $ unsafeSomeFinIntVal a
    else
        Nothing

someFinInt :: forall n m a. KnownFinInt (a :: FinInt n m) => SomeFinInt n m
someFinInt = SomeFinInt @n @m @a Proxy

someFinIntNegative :: forall n m a. (KnownNat n, KnownNat m, KnownNat a, a `CmpNat` (n + 1) ~ 'LT, a `CmpNat` 0 ~ 'GT) => SomeFinInt n m
someFinIntNegative = SomeFinInt @n @m @('Negative a) Proxy
someFinIntNonNegative :: forall n m a. (KnownNat n, KnownNat m, KnownNat a, a `CmpNat` m ~ 'LT) => SomeFinInt n m
someFinIntNonNegative = SomeFinInt @n @m @('NonNegative a) Proxy

sameFinInt :: forall n m (a :: FinInt n m) (b :: FinInt n m). (KnownFinInt a, KnownFinInt b) => Maybe (a :~: b)
sameFinInt =
    case (finIntSing @n @m @a, finIntSing @n @m @b) of
        (SFinInt a, SFinInt b) ->
            if a == b then
                Just (unsafeCoerce Refl)
            else
                Nothing

{-  -- TODO: Need Int first!
type family
    FinIntToInt (a :: FinInt n m) :: Int where
    FinIntToInt ('Negative a) = 'Int.Negative a
    FinIntToInt ('NonNegative a) = 'Int.NonNegative a

knownFinIntToKnownInt :: forall a. Dict (KnownFinInt a) -> Dict (KnownNat (FinIntToInt a))
knownFinIntToKnownInt Dict =
    reifyNat (finIntVal @a) $ \(Proxy :: Proxy n) ->
        case axiom @n @(FinIntToInt a) of
            Dict -> Dict
-}
{-
type family
    MaybeFinIntToNat (a :: FinInt n m) :: Nat where
    FinIntToNat ('Negative a) =
        TypeError ('Text "Negative integer (-" ':<>:
                   'ShowType a ':<>:
                   'Text ") cannot be converted to Nat")
    FinIntToNat ('NonNegative a) = a
-}
type family
    FinIntToMaybeNat (a :: FinInt n m) :: Maybe Nat where
    FinIntToMaybeNat ('Negative a) = 'Nothing
    FinIntToMaybeNat ('NonNegative a) = 'Just a

-- TODO: To match with Fin, we probably should have a working knownFinIntToKnownMaybeNat.
--  But it seems to require a proper KnownMaybeNat, in the same spirit as these modules.
--  Current workaround is to directly implement this logic in the singletons version of this module.
{-
newtype MagicNat r = MagicNat (forall (n :: Nat). KnownNat n => Proxy n -> r)

reifyNat :: forall r. Natural -> (forall (n :: Nat). KnownNat n => Proxy n -> r) -> r
reifyNat n k = unsafeCoerce (MagicNat k :: MagicNat r) n Proxy

axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))

class KnownMaybeNat (n :: Maybe Nat) where
instance KnownMaybeNat 'Nothing
instance KnownNat n => KnownMaybeNat ('Just n)

knownFinIntToKnownMaybeNat :: forall a. Dict (KnownFinInt a) -> Dict (KnownMaybeNat (FinIntToNat a))
knownFinIntToKnownMaybeNat Dict
    | val < 0 =
        case axiom @'Nothing @(FinIntToNat a) of
            Dict -> Dict
    | otherwise =
        reifyNat (fromInteger val) $ \(Proxy :: Proxy n) ->
            case axiom @('Just n) @(FinIntToNat a) of
                Dict -> Dict
    where
        val = finIntVal @a
-}

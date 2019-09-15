{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Data.Singletons.FinInt (
    Sing(SFinInt), SFinInt, withKnownFinInt,

    FinInt(..), KnownFinInt, finIntVal, SomeFinInt(..),
    someFinIntVal, someFinInt,
    FinIntToNat, knownFinIntToKnownNat,
    sFinIntVal, sFinIntToSNat) where

import Data.Singletons
import Data.Singletons.TypeLits (Nat, KnownNat, Sing(SNat), natVal)
import Data.Kind.FinInt
import Data.Kind
import Data.Constraint
import Control.Monad
import Numeric.Natural
import Data.Typeable
import Text.Read
import GHC.Show (appPrec, appPrec1)

import Data.Word


data instance Sing :: FinInt n m -> Type where
    SFinInt :: forall (n :: Nat) (m :: Nat) (a :: FinInt n m). KnownFinInt a => Sing a

instance KnownFinInt a => SingI a where
  sing = SFinInt

type SFinInt (n :: Nat) (m :: Nat) (a :: FinInt n m) = Sing a

withKnownFinInt :: forall a r. Sing a -> (KnownFinInt a => r) -> r
withKnownFinInt SFinInt f = f

-- TODO: Fix! Basically translate sign of Integer to/from 'Negative/'NonNegative.
--instance (KnownNat n, KnownNat m) => Show (SFinInt n m a) where
--    showsPrec p SFinInt =
--        showParen (p > appPrec) $
--            showString "SFinInt @" .
--            showsPrec appPrec1 (natVal @n Proxy) .
--            showString " @" .
--            showsPrec appPrec1 (natVal @m Proxy) .
--            showString " @" .
--            showParen True (
--                showString "'Negative " .  -- Or 'NonNegative... Need two cases here.
--                showsPrec appPrec1 (finIntVal @a)
--            )
--instance (KnownNat n, KnownNat m, KnownFinInt a) => Read (SFinInt n m a) where
--    readPrec = parens $ do
--        Ident "SFinInt" <- lexP
--        Punc "@" <- lexP
--        n <- prec appPrec1 $ readPrec @Natural
--        guard $ n == natVal @n Proxy
--        Punc "@" <- lexP
--        m <- prec appPrec1 $ readPrec @Natural
--        guard $ m == natVal @m Proxy
--        Punc "@" <- lexP
--        parens $ do
--            '\'' <- get
--            Ident "Negative" <- lexP  -- Or 'NonNegative... Need two cases here.
--            a <- prec appPrec1 $ readPrec @Natural
--            case someFinIntVal @n @m a of
--                Nothing -> mzero
--                Just (SomeFinInt (Proxy :: Proxy b)) ->
--                    case sameFinInt @n @m @a @b of
--                        Nothing -> mzero
--                        Just Refl -> return $ SFinInt @n @m @a

sFinIntVal :: Sing (x :: FinInt n m) -> Integer
sFinIntVal (SFinInt :: Sing x) = finIntVal @x

sFinIntToSNat :: Sing (x :: FinInt n m) -> Maybe (Sing (FinIntToNat x))
sFinIntToSNat (SFinInt :: Sing x) =
    case knownFinIntToKnownNat @x Dict of
        Nothing -> Nothing
        Just Dict -> Just SNat

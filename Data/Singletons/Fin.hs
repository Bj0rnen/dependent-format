{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}

module Data.Singletons.Fin (
    Sing(SFin), SFin, withKnownFin,

    Fin(..), KnownFin, finVal, SomeFin(..),
    someFinVal, someFin,
    FinToNat, knownFinToKnownNat,
    sFinVal, sFinToSNat) where

import Data.Singletons
import Data.Singletons.TypeLits (Nat, KnownNat, Sing(SNat), natVal)
import Data.Kind.Fin
import Data.Kind
import Data.Constraint
import Control.Monad
import Numeric.Natural
import Data.Typeable
import Text.Read
import GHC.Show (appPrec, appPrec1)

import Data.Word


data instance Sing :: Fin n -> Type where
    SFin :: forall (n :: Nat) (a :: Fin n). KnownFin a => Sing a

instance KnownFin a => SingI a where
  sing = SFin

-- TODO: Nat demotes to Natural, so is some kind of `Finite` type the way to go here?
-- TODO: Should in that case be in Data.Kind.Fin or Numeric.Finite. Should still be indexed on Nat, I guess.
-- TODO: Don't know how to limit its range in a nice way. Every operation returns a Maybe? Except `toNatural`.
--instance SingKind (Fin 256) where  -- TODO: Can we write this for any n?
--  type Demote (Fin 256) = Word8
--  fromSing (SFin :: Sing a) = fromIntegral $ finVal @a
--  toSing n =
--    case someFinVal $ fromIntegral n of
--        Nothing -> error $ show n ++ " out of bounds for Fin"  -- TODO: Not like this!
--        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SFin :: Sing a)

type SFin (n :: Nat) (a :: Fin n) = Sing a

withKnownFin :: forall a r. Sing a -> (KnownFin a => r) -> r
withKnownFin SFin f = f

instance KnownNat n => Show (SFin n a) where
    showsPrec p SFin =
        showParen (p > appPrec) $
            showString "SFin @" .
            showsPrec appPrec1 (natVal @n Proxy) .
            showString " @" .
            showParen True (
                showString "'Fin " .
                showsPrec appPrec1 (finVal @a)
            )
instance (KnownNat n, KnownFin a) => Read (SFin n a) where
    readPrec = parens $ do
        Ident "SFin" <- lexP
        Punc "@" <- lexP
        n <- prec appPrec1 $ readPrec @Natural
        guard $ n == natVal @n Proxy
        Punc "@" <- lexP
        parens $ do
            '\'' <- get
            Ident "Fin" <- lexP
            a <- prec appPrec1 $ readPrec @Natural
            case someFinVal @n a of
                Nothing -> mzero
                Just (SomeFin (Proxy :: Proxy b)) ->
                    case sameFin @n @a @b of
                        Nothing -> mzero
                        Just Refl -> return $ SFin @n @a

sFinVal :: Sing (x :: Fin n) -> Natural
sFinVal (SFin :: Sing x) = finVal @x

sFinToSNat :: Sing (x :: Fin n) -> Sing (FinToNat x)
sFinToSNat (SFin :: Sing x) = withDict (knownFinToKnownNat @x Dict) SNat

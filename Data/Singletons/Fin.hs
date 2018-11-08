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
    FinToNat, knownFinToKnownNat) where

import Data.Singletons
import Data.Kind.Fin
import GHC.TypeNats
import Data.Kind
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

instance SingKind (Fin 256) where  -- TODO: Can we write
  type Demote (Fin 256) = Word8
  fromSing (SFin :: Sing a) = fromIntegral $ finVal @a
  toSing n =
    case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin"  -- TODO: Not like this!
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SFin :: Sing a)

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

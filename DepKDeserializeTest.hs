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
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RoleAnnotations #-}

module DepKDeserializeTest where

import DepKDeserialize
import Vector
import DepState
import Knowledge
import DepLevel

import Data.Singletons
import Data.Singletons.TH
import GHC.TypeNats
import Data.Singletons.TypeLits
import Data.Kind

import qualified GHC.Generics as GHC hiding (from, to)
import Generics.SOP hiding (Sing, Nil, SingI, sing)
import qualified Generics.SOP as SOP
import Generics.SOP.Classes (Same)
import GHC.TypeLits (TypeError(..), ErrorMessage(..))
import           Generics.Kind hiding (Nat, (:~:))
import qualified Generics.Kind as K
import Generics.Kind.TH

import Data.Proxy
import Data.Constraint
import Data.Constraint.Nat
import Unsafe.Coerce
import GHC.Types (Any)
import Data.Coerce
import Data.Functor.Const

import Data.Word
import Data.Bits
import Numeric.Natural
import Data.Kind.Fin (ltNat, predecessor, subNat)
import Data.Singletons.Fin

import Data.Reflection

import Control.Monad.State
import Control.Monad.Except


{-
-- Example of the flow of atoms between depKDeserialize and depKDeserializeK.

depKDeserialize @(Nat -> Type) @SameVarL0R1
    (Proxy @(AtomCons Var3 AtomNil))
    (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU KnowledgeNil))))
==>
depKDeserializeK @(Nat -> Type) @(Field (Kon L0R1 :@: Var0 :@: Var0))
    (Proxy @(AtomCons Var3 AtomNil))
    (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU KnowledgeNil))))
==>
depKDeserialize @(Nat -> Nat -> Type) @L0R1
    (Proxy @(AtomCons Var3 (AtomCons Var3 AtomNil)))
    (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU KnowledgeNil))))


DereferenceAtomList (AtomCons Var3 AtomNil) (AtomCons Var0 (AtomCons Var0 AtomNil))
~
AtomCons Var3 (AtomCons Var3 AtomNil)
-}


data L0R1 (size0 :: Nat) (size1 :: Nat) = L0R1
    { size0 :: Sing size0
    , arr1  :: Vector Word8 size1
    } deriving (Show)
$(deriveGenericK ''L0R1)

deriving instance DepKDeserialize L0R1
deriving instance SingI size0 => DepKDeserialize (L0R1 size0)
deriving instance (SingI size0, SingI size1) => DepKDeserialize (L0R1 size0 size1)

testL0R1SameVar :: String
testL0R1SameVar =
    case evalState
            (runExceptT $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1DifferentVars :: String
testL0R1DifferentVars =
    case evalState
            (runExceptT $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))) (KnowledgeCons KnowledgeU (KnowledgeCons (KnowledgeK (sing @5)) KnowledgeNil)))
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1Kons :: String
testL0R1Kons =
    case evalState
            (runExceptT $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons ('Kon 2) (AtomCons ('Kon 5) AtomNil))) KnowledgeNil)
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1KonsContradictory :: String
testL0R1KonsContradictory =
    case evalState
            (runExceptT $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons ('Kon 1) (AtomCons ('Kon 5) AtomNil))) KnowledgeNil)
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1AlreadyKnown :: String
testL0R1AlreadyKnown =
    case evalState
            (runExceptT $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))) (KnowledgeCons (KnowledgeK (sing @2)) KnowledgeNil))
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a


testL0R1AlreadyKnownContradictory :: String
testL0R1AlreadyKnownContradictory =
    case evalState
            (runExceptT $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))) (KnowledgeCons (KnowledgeK (sing @1)) KnowledgeNil))
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1SameVarK :: String
testL0R1SameVarK =
    case evalState
            (runExceptT $ depKDeserializeK @_ @(Field (Sing :$: Var0) :*: Field (Vector Word8 :$: Var1)) (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyKK a, _) -> show a

testL0R1Of2AndKnown3 :: String
testL0R1Of2AndKnown3 =
    case evalState
            (runExceptT $ depKDeserialize @_ @(L0R1 2) (Proxy @(AtomCons Var0 AtomNil)) (KnowledgeCons (KnowledgeK (sing @3)) KnowledgeNil))
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1Of2And3 :: String
testL0R1Of2And3 =
    case evalState
            (runExceptT $ depKDeserialize @_ @(L0R1 2 3) (Proxy @AtomNil) KnowledgeNil)
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a


data SameVarL0R1 size = SameVarL0R1
    { l0r1 :: L0R1 size size
    } deriving (Show)
$(deriveGenericK ''SameVarL0R1)

deriving instance DepKDeserialize SameVarL0R1
deriving instance SingI size => DepKDeserialize (SameVarL0R1 size)

testSameVarL0R1Unkown :: String
testSameVarL0R1Unkown =
    case evalState
            (runExceptT $ depKDeserialize @_ @SameVarL0R1 (Proxy @(AtomCons Var0 AtomNil)) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a


data SameExistentialVarL0R1 = forall size. SameExistentialVarL0R1
    { l0r1 :: L0R1 size size
    }
deriving instance Show SameExistentialVarL0R1
$(deriveGenericK ''SameExistentialVarL0R1)

deriving instance DepKDeserialize SameExistentialVarL0R1

testSameExistentialVarL0R1 :: String
testSameExistentialVarL0R1 =
    case evalState
            (runExceptT $ depKDeserialize @_ @SameExistentialVarL0R1 (Proxy @AtomNil) KnowledgeNil)
            [2,3,4,5,6,7] of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testSameExistentialVarL0R1Simple :: (Either DeserializeError SameExistentialVarL0R1, [Word8])
testSameExistentialVarL0R1Simple = runState (runExceptT $ deserialize @SameExistentialVarL0R1) [2,3,4,5,6,7]


data EmptyRecord = EmptyRecord
    {} deriving (Show)
$(deriveGenericK ''EmptyRecord)

deriving instance DepKDeserialize EmptyRecord

testEmptyRecordSimple :: (Either DeserializeError EmptyRecord, [Word8])
testEmptyRecordSimple = runState (runExceptT $ deserialize @EmptyRecord) [2,3,4,5,6,7]


data PlainField = PlainField
    { word16 :: Word16
    } deriving (Show)
$(deriveGenericK ''PlainField)

deriving instance DepKDeserialize PlainField

testPlainFieldSimple :: (Either DeserializeError PlainField, [Word8])
testPlainFieldSimple = runState (runExceptT $ deserialize @PlainField) [2,3,4,5,6,7]


data ExistentialL0L0 = forall (size :: Nat). ExistentialL0L0
    { size0 :: Sing size
    , size1 :: Sing size
    }
deriving instance Show ExistentialL0L0
$(deriveGenericK ''ExistentialL0L0)

deriving instance DepKDeserialize ExistentialL0L0

testExistentialL0L0ContradictorySimple :: (Either DeserializeError ExistentialL0L0, [Word8])
testExistentialL0L0ContradictorySimple = runState (runExceptT $ deserialize @ExistentialL0L0) [2,3,4,5,6,7]


data ExistentialL0L1R0R1 = forall size0 size1. ExistentialL0L1R0R1
    { size0 :: Sing size0
    , size1 :: Sing size1
    , vect0 :: Vector Word8 size0
    , vect1 :: Vector Word8 size1
    }
deriving instance Show ExistentialL0L1R0R1
$(deriveGenericK ''ExistentialL0L1R0R1)

deriving instance DepKDeserialize ExistentialL0L1R0R1

testExistentialL0L1R0R1Simple :: (Either DeserializeError ExistentialL0L1R0R1, [Word8])
testExistentialL0L1R0R1Simple = runState (runExceptT $ deserialize @ExistentialL0L1R0R1) [1,2,3,4,5,6]


(%+) :: Sing n -> Sing m -> Sing (n + m)
(SNat :: Sing n) %+ (SNat :: Sing m) = SNat \\ plusNat @n @m
$(genDefunSymbols [''(+)])


$(singletons [d|
  onePlus :: Nat -> Nat
  onePlus a = 1 + a
  |])

data RecordWithOnePlus = forall (a :: Nat) (b :: Nat). RecordWithOnePlus
    { a :: Sing a
    , b :: Let OnePlusSym0 a b
    , v :: Vector Word8 b
    }
deriving instance Show RecordWithOnePlus
$(deriveGenericK ''RecordWithOnePlus)

deriving instance DepKDeserialize RecordWithOnePlus

testRecordWithOnePlus :: (Either DeserializeError RecordWithOnePlus, [Word8])
testRecordWithOnePlus = runState (runExceptT $ deserialize @RecordWithOnePlus) [1,2,3,4,5,6]

$(singletons [d|
  plus :: Nat -> Nat -> Nat
  plus a b = a + b
  |])

data RecordWithPlus = forall (a :: Nat) (b :: Nat) (f :: Nat ~> Nat) (c :: Nat). RecordWithPlus
    { a :: Sing a
    , b :: Sing b
    , f :: Let PlusSym0 a f
    , c :: Let f b c
    , v :: Vector Word8 c
    }
deriving instance Show RecordWithPlus
$(deriveGenericK ''RecordWithPlus)

deriving instance DepKDeserialize RecordWithPlus

testRecordWithPlus :: (Either DeserializeError RecordWithPlus, [Word8])
testRecordWithPlus = runState (runExceptT $ deserialize @RecordWithPlus) [1,2,3,4,5,6]


data RecordWithPlus2 = forall (a :: Nat) (b :: Nat) (f :: Nat ~> Nat) (c :: Nat). RecordWithPlus2
    { a :: Sing a
    , b :: Sing b
    , c :: Let2 PlusSym0 a b c
    , v :: Vector Word8 c
    }
deriving instance Show RecordWithPlus2
$(deriveGenericK ''RecordWithPlus2)

deriving instance DepKDeserialize RecordWithPlus2

testRecordWithPlus2 :: (Either DeserializeError RecordWithPlus2, [Word8])
testRecordWithPlus2 = runState (runExceptT $ deserialize @RecordWithPlus2) [1,2,3,4,5,6]

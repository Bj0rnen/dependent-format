{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}

module DepKDeserializeTest where

import DepKDeserialize
import Vector
import Knowledge

import Data.Singletons.TH
import GHC.TypeNats

import           Generics.Kind hiding (Nat, (:~:))
import Generics.Kind.TH

import Data.Word

import Control.Monad.State
import Control.Monad.Indexed.State


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
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))))
            (KnowledgeCons KnowledgeU KnowledgeNil, [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1DifferentVars :: String
testL0R1DifferentVars =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))))
            (KnowledgeCons KnowledgeU (KnowledgeCons (KnowledgeK (sing @5)) KnowledgeNil), [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1Kons :: String
testL0R1Kons =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons ('Kon 2) (AtomCons ('Kon 5) AtomNil))))
            (KnowledgeNil, [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1KonsContradictory :: String
testL0R1KonsContradictory =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons ('Kon 1) (AtomCons ('Kon 5) AtomNil))))
            (KnowledgeNil, [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1AlreadyKnown :: String
testL0R1AlreadyKnown =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))))
            ((KnowledgeCons (KnowledgeK (sing @2)) KnowledgeNil), [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a


testL0R1AlreadyKnownContradictory :: String
testL0R1AlreadyKnownContradictory =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))))
            ((KnowledgeCons (KnowledgeK (sing @1)) KnowledgeNil), [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1SameVarK :: String
testL0R1SameVarK =
    case runIxStateT
            (runIxGet $ depKDeserializeK @_ @(Field (Sing :$: Var0) :*: Field (Vector Word8 :$: Var1)) (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))))
            (KnowledgeCons KnowledgeU KnowledgeNil, [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyKK a, _) -> show a

testL0R1Of2AndKnown3 :: String
testL0R1Of2AndKnown3 =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @(L0R1 2) (Proxy @(AtomCons Var0 AtomNil)))
            (KnowledgeCons (KnowledgeK (sing @3)) KnowledgeNil, [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testL0R1Of2And3 :: String
testL0R1Of2And3 =
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @(L0R1 2 3) (Proxy @AtomNil))
            (KnowledgeNil, [2,3,4,5,6,7]) of
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
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @SameVarL0R1 (Proxy @(AtomCons Var0 AtomNil)))
            (KnowledgeCons KnowledgeU KnowledgeNil, [2,3,4,5,6,7]) of
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
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @SameExistentialVarL0R1 (Proxy @AtomNil))
            (KnowledgeNil, [2,3,4,5,6,7]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

testSameExistentialVarL0R1Simple :: (Either DeserializeError (SameExistentialVarL0R1, [Word8]))
testSameExistentialVarL0R1Simple = runStateT (deserialize @SameExistentialVarL0R1) [2,3,4,5,6,7]


data EmptyRecord = EmptyRecord
    {} deriving (Show)
$(deriveGenericK ''EmptyRecord)

deriving instance DepKDeserialize EmptyRecord

testEmptyRecordSimple :: (Either DeserializeError (EmptyRecord, [Word8]))
testEmptyRecordSimple = runStateT (deserialize @EmptyRecord) [2,3,4,5,6,7]


data PlainField = PlainField
    { word16 :: Word16
    } deriving (Show)
$(deriveGenericK ''PlainField)

deriving instance DepKDeserialize PlainField

testPlainFieldSimple :: (Either DeserializeError (PlainField, [Word8]))
testPlainFieldSimple = runStateT (deserialize @PlainField) [2,3,4,5,6,7]


data ExistentialL0L0 = forall (size :: Nat). ExistentialL0L0
    { size0 :: Sing size
    , size1 :: Sing size
    }
deriving instance Show ExistentialL0L0
$(deriveGenericK ''ExistentialL0L0)

deriving instance DepKDeserialize ExistentialL0L0

testExistentialL0L0ContradictorySimple :: (Either DeserializeError (ExistentialL0L0, [Word8]))
testExistentialL0L0ContradictorySimple = runStateT (deserialize @ExistentialL0L0) [2,3,4,5,6,7]


data ExistentialL0L1R0R1 = forall size0 size1. ExistentialL0L1R0R1
    { size0 :: Sing size0
    , size1 :: Sing size1
    , vect0 :: Vector Word8 size0
    , vect1 :: Vector Word8 size1
    }
deriving instance Show ExistentialL0L1R0R1
$(deriveGenericK ''ExistentialL0L1R0R1)

deriving instance DepKDeserialize ExistentialL0L1R0R1

testExistentialL0L1R0R1Simple :: (Either DeserializeError (ExistentialL0L1R0R1, [Word8]))
testExistentialL0L1R0R1Simple = runStateT (deserialize @ExistentialL0L1R0R1) [1,2,3,4,5,6]

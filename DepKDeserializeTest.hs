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
import Serialize
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
    } deriving (Show, GHC.Generic)
-- $(deriveGenericK 'L0R1)  -- BUG: Not this alone, but upon deriving DepKDeserialize, GHC hangs. Doesn't happen with manually written GenericK instances...
instance GenericK L0R1 (size0 :&&: size1 :&&: 'LoT0) where
    type RepK L0R1 = Field (Sing :$: Var0) :*: Field (Vector Word8 :$: Var1)
instance GenericK (L0R1 size0) (size1 :&&: 'LoT0) where
    type RepK (L0R1 size0) = Field ('Kon (Sing size0)) :*: Field (Vector Word8 :$: Var0)
instance GenericK (L0R1 size0 size1) 'LoT0 where
    type RepK (L0R1 size0 size1) = Field ('Kon (Sing size0)) :*: Field ('Kon (Vector Word8 size1))

deriving instance DepKDeserialize L0R1
deriving instance SingI size0 => DepKDeserialize (L0R1 size0)
deriving instance (SingI size0, SingI size1) => DepKDeserialize (L0R1 size0 size1)

testL0R1SameVar :: String
testL0R1SameVar =
    case evalState
            (depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

testL0R1DifferentVars :: String
testL0R1DifferentVars =
    case evalState
            (depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))) (KnowledgeCons KnowledgeU (KnowledgeCons (KnowledgeK (sing @5)) KnowledgeNil)))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

testL0R1Kons :: String
testL0R1Kons =
    case evalState
            (depKDeserialize @_ @L0R1 (Proxy @(AtomCons ('Kon 2) (AtomCons ('Kon 5) AtomNil))) KnowledgeNil)
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

testL0R1KonsContradictory :: String
testL0R1KonsContradictory =
    case evalState
            (depKDeserialize @_ @L0R1 (Proxy @(AtomCons ('Kon 1) (AtomCons ('Kon 5) AtomNil))) KnowledgeNil)
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

testL0R1AlreadyKnown :: String
testL0R1AlreadyKnown =
    case evalState
            (depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))) (KnowledgeCons (KnowledgeK (sing @2)) KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a


testL0R1AlreadyKnownContradictory :: String
testL0R1AlreadyKnownContradictory =
    case evalState
            (depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))) (KnowledgeCons (KnowledgeK (sing @1)) KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

testL0R1SameVarK :: String
testL0R1SameVarK =
    case evalState
            (depKDeserializeK @_ @(Field (Sing :$: Var0) :*: Field (Vector Word8 :$: Var1)) (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyKK a, _) -> show a

testL0R1Of2AndKnown3 :: String
testL0R1Of2AndKnown3 =
    case evalState
            (depKDeserialize @_ @(L0R1 2) (Proxy @(AtomCons Var0 AtomNil)) (KnowledgeCons (KnowledgeK (sing @3)) KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) show a

testL0R1Of2And3 :: String
testL0R1Of2And3 =
    case evalState
            (depKDeserialize @_ @(L0R1 2 3) (Proxy @AtomNil) KnowledgeNil)
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) show a


data SameVarL0R1 size = SameVarL0R1
    { l0r1 :: L0R1 size size
    } deriving (Show, GHC.Generic)
-- $(deriveGenericK 'SameVarL0R1)
instance GenericK SameVarL0R1 (size :&&: 'LoT0) where
    type RepK SameVarL0R1 = Field (L0R1 :$: Var0 :@: Var0)
instance GenericK (SameVarL0R1 size) 'LoT0 where
    type RepK (SameVarL0R1 size) = Field ('Kon (L0R1 size size))

deriving instance DepKDeserialize SameVarL0R1
deriving instance SingI size => DepKDeserialize (SameVarL0R1 size)

testSameVarL0R1Unkown :: String
testSameVarL0R1Unkown =
    case evalState
            (depKDeserialize @_ @SameVarL0R1 (Proxy @(AtomCons Var0 AtomNil)) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a


data SameExistentialVarL0R1 = forall size. SameExistentialVarL0R1
    { l0r1 :: L0R1 size size
    }
deriving instance Show SameExistentialVarL0R1
instance GenericK SameExistentialVarL0R1 'LoT0 where
    type RepK SameExistentialVarL0R1 = Exists Nat (Field (L0R1 :$: Var0 :@: Var0))
    fromK (SameExistentialVarL0R1 a) = Exists (Field a)
    toK (Exists (Field a)) = SameExistentialVarL0R1 a

deriving instance DepKDeserialize SameExistentialVarL0R1

testSameExistentialVarL0R1 :: String
testSameExistentialVarL0R1 =
    case evalState
            (depKDeserialize @_ @SameExistentialVarL0R1 (Proxy @AtomNil) KnowledgeNil)
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

testSameExistentialVarL0R1Simple :: SameExistentialVarL0R1
testSameExistentialVarL0R1Simple = evalState (dep0Deserialize @SameExistentialVarL0R1) [2,3,4,5,6,7]

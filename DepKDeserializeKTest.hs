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

module DepKDeserializeKTest where

import DepKDeserializeK
import Vector
import DepState
import Knowledge

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

import Exinst
import Data.Reflection


trySingK1 :: String  -- Why is annotation neccessary? Why are you doing this, type families!!?!??
trySingK1 =
    case depKDeserializeK @(Nat -> Nat -> Type) @(Field (Kon Sing :@: Var 'VZ)) (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil)) [2,3,4] of
        (PartiallyKnownK (ExplicitPartialKnowledgeCons (KnowledgeK s) (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil)) (Field p), bs) ->
            show (p, bs)
trySingK2 :: String  -- Why is annotation neccessary? Why are you doing this, type families!!?!??
trySingK2 =
    case depKDeserializeK @(Nat -> Nat -> Type) @(Field (Kon Sing :@: Var ('VS 'VZ))) (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil)) [2,3,4] of
        (PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeK s) ExplicitPartialKnowledgeNil)) (Field p), bs) ->
            show (p, bs)

tryVectorK :: String
tryVectorK =
    case depKDeserializeK @(Nat -> Nat -> Type) @(Field (Kon (Vector Word8) :@: Var ('VS 'VZ))) (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeK (SNat @2)) ExplicitPartialKnowledgeNil)) [2,3,4] of
        (PartiallyKnownK _ (Field p), bs) ->
            show (p, bs)

tryItAgain :: String
tryItAgain =
    case depKDeserializeK @(Nat -> Nat -> Type) @((Field (Kon Sing :@: Var ('VS 'VZ))) :*: (Field (Kon (Vector Word8) :@: Var ('VS 'VZ)))) (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil)) [2,3,4] of
        (PartiallyKnownK _ (Field sng :*: Field vec), bs) ->
            show (sng, vec, bs)
shouldFailAgain :: String
shouldFailAgain =
    case depKDeserializeK @(Nat -> Nat -> Type) @((Field (Kon Sing :@: Var ('VS 'VZ))) :*: (Field (Kon Sing :@: Var ('VS 'VZ)))) (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil)) [2,3,4] of
        (PartiallyKnownK _ (Field sng1 :*: Field sng2), bs) ->
            show (sng1, sng2, bs)
tryThis :: String
tryThis =  -- TODO: I think this shouldn't be a problem
    case depKDeserializeK @(Nat -> Nat -> Type) @(( (Field (Kon Sing           :@: Var VZ) :*: Field (Kon Sing           :@: Var (VS VZ)))
                                                   :*:
                                                    (Field (Kon (Vector Word8) :@: Var VZ) :*: Field (Kon (Vector Word8) :@: Var (VS VZ)))))
            (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil)) [1,2,3,4,5,6] of
        (PartiallyKnownK _ ((Field s1 :*: Field s2) :*: (Field v1 :*: Field v2)), bs) -> show ((s1, s2, v1, v2), bs)


data NewL1L2R1R2 size1 size2 = NewL1L2R1R2
    { size1 :: Sing size1
    , size2 :: Sing size2
    , arr1  :: Vector Word8 size1
    , arr2  :: Vector Word8 size2
    } deriving (GHC.Generic, Show)
      --deriving DepKDeserializeK via ??? NewL1L2R1R2
$(deriveGenericK 'NewL1L2R1R2)

testDeserializeSomeDep2NewL1L2R1R2 :: (PartiallyKnownK (Nat -> Nat -> Type) (RepK NewL1L2R1R2) ('DS 'Known ('DS 'Known 'DZ)), [Word8])
testDeserializeSomeDep2NewL1L2R1R2 =
    case fillUnkowns of
        SomePartialKnowledge filled ->
            depKDeserializeK filled [1,2,3,4,5,6]
showTestDeserializeSomeDep2NewL1L2R1R2 :: String
showTestDeserializeSomeDep2NewL1L2R1R2 =
    case testDeserializeSomeDep2NewL1L2R1R2 of
        (PartiallyKnownK ds f, bs) -> show (f, bs)
-- TODO: Show instance for ExplicitPartiallyKnowledge.

data L1L2 (size1 :: Nat) (size2 :: Nat) = L1L2
    { size1 :: Sing size1
    , size2 :: Sing size2
    } deriving (GHC.Generic, Show)
$(deriveGenericK 'L1L2)
deriving via Generic2KWrapper L1L2 v1 v2 instance (GettingVth v1, GettingVth v2, AddingVth v1, AddingVth v2
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Known   v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Known   v2)) => DepKDeserializeK (Field (Kon L1L2 :@: Var v1 :@: Var v2))

data R1R2 (size1 :: Nat) (size2 :: Nat) = R1R2
    { arr1 :: Vector Word8 size1
    , arr2 :: Vector Word8 size2
    } deriving (GHC.Generic, Show)
$(deriveGenericK 'R1R2)
deriving via Generic2KWrapper R1R2 v1 v2 instance (GettingVth v1, GettingVth v2, AddingVth v1, AddingVth v2
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Known   v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Known   v2)) => DepKDeserializeK (Field (Kon R1R2 :@: Var v1 :@: Var v2))

data ComposedL1L2R1R2 size1 size2 = ComposedL1L2R1R2
    { l1l2 :: L1L2 size1 size2
    , r1r2 :: R1R2 size1 size2
    } deriving (GHC.Generic, Show)
$(deriveGenericK 'ComposedL1L2R1R2)
deriving via Generic2KWrapper ComposedL1L2R1R2 v1 v2 instance (GettingVth v1, GettingVth v2, AddingVth v1, AddingVth v2
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Known   v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Known   v2)) => DepKDeserializeK (Field (Kon ComposedL1L2R1R2 :@: Var v1 :@: Var v2))

showTestDeserializeSomeDep2ComposedL1L2R1R2 :: String
showTestDeserializeSomeDep2ComposedL1L2R1R2 =
    case fillUnkowns of
        SomePartialKnowledge filled ->
            case depKDeserializeK @_ @(RepK ComposedL1L2R1R2) filled [1,2,3,4,5,6] of
                (PartiallyKnownK ds f, bs) ->
                    show (f, bs)


data L1R2 (size1 :: Nat) (size2 :: Nat) = L1R2
    { size1 :: Sing size1
    , arr2  :: Vector Word8 size2
    } deriving (GHC.Generic, Show)
$(deriveGenericK 'L1R2)
deriving via Generic2KWrapper L1R2 v1 v2 instance (GettingVth v1, GettingVth v2, AddingVth v1, AddingVth v2
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Known   v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Known   v2)) => DepKDeserializeK (Field (Kon L1R2 :@: Var v1 :@: Var v2))

data ReuseVar0 (size1 :: Nat) = ReuseVar0
    { l1r2 :: L1R2 size1 size1
    } deriving (GHC.Generic, Show)
$(deriveGenericK 'ReuseVar0)
deriving via Generic1KWrapper ReuseVar0 v1 instance (GettingVth v1, AddingVth v1) => DepKDeserializeK (Field (Kon ReuseVar0 :@: Var v1))

{-}
-- TODO: Ideally, this should actually work, because in L1R2, size1 comes before arr2 and if they are the same tyvar, what's required has been learnt.
-- TODO: Most likely, this is a problem with DepStateRequirements not quite composing properly.
showTestDeserializeSomeDep2ReuseVar0 :: String
showTestDeserializeSomeDep2ReuseVar0 =
    -- NOTE: This alternative compiles.
    --case learnVth @_ @_ @'VZ (SNat @1) of
    case fillUnkowns of
        SomePartialKnowledge filled ->
            case depKDeserializeK @_ @(RepK ReuseVar0) filled [1,2,3,4,5,6] of
                (PartiallyKnownK ds f, bs) ->
                    show (f, bs)

-- Sooo...
--
-- > :kind! DepStateRequirements (Generic2KWrapper L1R2 'VZ 'VZ) ('DS 'Unknown ('DS 'Unknown 'DZ))
-- DepStateRequirements (Generic2KWrapper L1R2 'VZ 'VZ) ('DS 'Unknown ('DS 'Unknown 'DZ)) :: Constraint
-- = (MergePartialKnowledge
--      ('DS 'Unknown ('DS 'Unknown 'DZ)) ('DS 'Known ('DS 'Unknown 'DZ)),
--    () :: Constraint, 'Unknown ~ 'Known)
--
-- > :kind! DepStateRequirements (RepK L1R2) ('DS 'Unknown ('DS 'Unknown 'DZ))
-- DepStateRequirements (RepK L1R2) ('DS 'Unknown ('DS 'Unknown 'DZ)) :: Constraint
-- = (MergePartialKnowledge
--      ('DS 'Unknown ('DS 'Unknown 'DZ)) ('DS 'Known ('DS 'Unknown 'DZ)),
--    () :: Constraint, 'Unknown ~ 'Known)
--
-- This latter one I actually agree that it's supposed to fail, which it does. But the former one, that one I would want to not go bad.
-- The former reduces to the latter via:
--
-- DepStateRequirements (Generic2KWrapper f v1 v2) ds =
--     DepStateRequirements (RepK f) ('DS (GetVthDepState v1 ds) ('DS (GetVthDepState v2 ds) 'DZ))
--
-- That is, Var0's DepState ('Unknown) gets copied into both places of the LoT that (RepK L1R2) gets. And upon doing that,
-- it "forgets" that these DepStates correspond to the same variable.
--
-- For reference, (RepK L1R2) is roughly:
-- Field ('Kon Sing ':@: Var0) :*: Field ('Kon (Vector Word8) ':@: Var1)
--
-- At that point, the DepState at Var1 is of course not going to update when deserializing the Sing.
--
-- Is there something we can do about this? How hard would it be to fix? Does it make sense to do?

--}--}--}--}--}--}

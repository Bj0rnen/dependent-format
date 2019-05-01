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

module DepKDeserializeK where

import Serialize
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

import Data.Reflection


data DepStateList d where
    DZ :: DepStateList Type
    DS :: DepState -> DepStateList xs -> DepStateList (x -> xs)

data ExplicitPartialKnowledge (ks :: Type) (xs :: LoT ks) (ds :: DepStateList ks) where
    ExplicitPartialKnowledgeNil  :: ExplicitPartialKnowledge Type LoT0 'DZ
    ExplicitPartialKnowledgeCons :: Knowledge d (x :: a) -> ExplicitPartialKnowledge ks xs ds -> ExplicitPartialKnowledge (a -> ks) (x :&&: xs) ('DS d ds)

data SomePartialKnowledge (ks :: Type) (ds :: DepStateList ks) where
    SomePartialKnowledge :: ExplicitPartialKnowledge ks xs ds -> SomePartialKnowledge ks ds

data PartiallyKnownK (ks :: Type) (f :: LoT ks -> Type) (ds :: DepStateList ks) where
    PartiallyKnownK :: ExplicitPartialKnowledge ks xs ds -> f xs -> PartiallyKnownK ks f ds

{-
myDemote :: forall k (a :: k). SingKind k => Sing a -> Demote k
myDemote s = withSingI s (demote @a)

vectorToList :: Vector a n -> [a]
vectorToList Nil = []
vectorToList (a :> as) = a : vectorToList as

class PartialKnowledgeToSomeSing (v :: TyVar ks k) (ds :: DepStateList ks) where
    partialKnowledgeToSomeSing :: forall xs. ExplicitPartialKnowledge ks xs ds -> SomeSing k
instance PartialKnowledgeToSomeSing 'VZ ('DS 'Known ds) where
    partialKnowledgeToSomeSing a =
        case a of
            ExplicitPartialKnowledgeCons (KnowledgeK s) _ ->
                SomeSing s
instance PartialKnowledgeToSomeSing v ds => PartialKnowledgeToSomeSing ('VS (v :: TyVar ks k)) ('DS knwlg (ds :: DepStateList ks)) where
    partialKnowledgeToSomeSing a =
        case a of
            ExplicitPartialKnowledgeCons _ knwlg ->
                partialKnowledgeToSomeSing @ks @k @v knwlg

partiallyKnownToSomeSing :: forall (v :: TyVar ks k) f ds. PartialKnowledgeToSomeSing v ds => PartiallyKnownK ks f ds -> SomeSing k
partiallyKnownToSomeSing a =
    case a of
        PartiallyKnownK knowledge _ ->
            partialKnowledgeToSomeSing @ks @k @v knowledge


examplePartiallyKnownSingVar2 :: PartiallyKnownK (k -> Nat -> Type) (Field (Kon (Sing :: Nat -> Type) :@: Var ('VS 'VZ))) ('DS 'Unknown ('DS 'Known 'DZ))
examplePartiallyKnownSingVar2 = PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeK SNat) ExplicitPartialKnowledgeNil)) (Field (SNat @1337))

examplePartiallyKnownSingVar2Unknown :: PartiallyKnownK (k -> Nat -> Type) (Field (Kon (Sing :: Nat -> Type) :@: Var ('VS 'VZ))) ('DS 'Unknown ('DS 'Unknown 'DZ))
examplePartiallyKnownSingVar2Unknown = PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeU) ExplicitPartialKnowledgeNil)) (Field (SNat @1337))

examplePartiallyKnownVecVar2 :: PartiallyKnownK (k -> Nat -> Type) (Field (Kon (Vector Word8 :: Nat -> Type) :@: Var ('VS 'VZ))) ('DS 'Unknown ('DS 'Known 'DZ))
examplePartiallyKnownVecVar2 = PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeK SNat) ExplicitPartialKnowledgeNil)) (Field (0 :> 1 :> Nil))

examplePartiallyKnownVecVar2Unknown :: PartiallyKnownK (k -> Nat -> Type) (Field (Kon (Vector Word8 :: Nat -> Type) :@: Var ('VS 'VZ))) ('DS 'Unknown ('DS 'Unknown 'DZ))
examplePartiallyKnownVecVar2Unknown = PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeU) ExplicitPartialKnowledgeNil)) (Field (0 :> 1 :> Nil))

-- Can do:
getKnownExampleSing :: SomeSing Nat
getKnownExampleSing = partiallyKnownToSomeSing @_ @_ @('VS 'VZ) examplePartiallyKnownSingVar2

getKnownExampleVec :: SomeSing Nat
getKnownExampleVec = partiallyKnownToSomeSing @_ @_ @('VS 'VZ) examplePartiallyKnownVecVar2

-- Can't do:
--getUnknownExampleSing :: SomeSing Nat
--getUnknownExampleSing = partiallyKnownToSomeSing @_ @_ @('VS 'VZ) examplePartiallyKnownSingVar2Unknown
--
--getUnknownExampleList :: SomeSing Nat
--getUnknownExampleList = partiallyKnownToSomeSing @_ @_ @('VS 'VZ) examplePartiallyKnownVecVar2Unknown
-}

type family
    FillUnkowns (ks :: Type) :: DepStateList ks where
    FillUnkowns Type = 'DZ
    FillUnkowns (k -> ks) = 'DS 'Unknown (FillUnkowns ks)
class FillingUnknowns (ks :: Type) where
    fillUnkowns :: SomePartialKnowledge ks (FillUnkowns ks)
instance FillingUnknowns Type where
    fillUnkowns = SomePartialKnowledge ExplicitPartialKnowledgeNil
instance FillingUnknowns ks => FillingUnknowns (k -> ks) where
    fillUnkowns =
        case fillUnkowns of
            SomePartialKnowledge filled ->
                SomePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU filled)

type family
    AddVth (d :: DepState) (v :: TyVar ks k) :: DepStateList ks where
    AddVth d ('VZ :: TyVar (k -> ks) k) = 'DS d (FillUnkowns ks)
    AddVth d ('VS v) = 'DS 'Unknown (AddVth d v)
class AddingVth (v :: TyVar ks k) where
    addVth :: forall d. Knwlg d k -> SomePartialKnowledge ks (AddVth d v)
instance FillingUnknowns ks => AddingVth ('VZ :: TyVar (k -> ks) k) where
    addVth k =
        withKnwlg k $ \k' ->
            case fillUnkowns of
                SomePartialKnowledge filled ->
                    SomePartialKnowledge (ExplicitPartialKnowledgeCons k' filled)
instance AddingVth v => AddingVth ('VS v) where
    addVth k =
        withKnwlg k $ \k' ->
            case addVth @_ @_ @v k of
                SomePartialKnowledge learned ->
                    SomePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU learned)

learnVth :: forall ks k (v :: TyVar ks k). AddingVth v => forall (a :: k). Sing a -> SomePartialKnowledge ks (AddVth 'Known v)
learnVth s = addVth @_ @_ @v (KnwlgK s)

type family
    GetVthDepState (v :: TyVar ks k) (ds :: DepStateList ks) :: DepState where
    GetVthDepState 'VZ ('DS d _) = d
    GetVthDepState ('VS v) ('DS _ ds) = GetVthDepState v ds
class GettingVth (v :: TyVar ks k) where
    getVth :: forall ds. SomePartialKnowledge ks ds -> Knwlg (GetVthDepState v ds) k
instance GettingVth 'VZ where
    getVth (SomePartialKnowledge (ExplicitPartialKnowledgeCons k _)) = knowledgeToKnwlg k
instance GettingVth v => GettingVth ('VS v) where
    getVth (SomePartialKnowledge (ExplicitPartialKnowledgeCons _ ks)) = getVth @_ @_ @v (SomePartialKnowledge ks)

knowVth :: forall ks k (v :: TyVar ks k) (ds :: DepStateList ks). GettingVth v => forall ds. GetVthDepState v ds ~ 'Known => SomePartialKnowledge ks ds -> SomeSing k
knowVth pk = case getVth @_ @_ @v pk of KnwlgK s -> SomeSing s


class MergePartialKnowledge (ds1 :: DepStateList ks) (ds2 :: DepStateList ks) where
    type MergedPartialKnowledge ds1 ds2 :: DepStateList ks
    mergePartialKnowledge :: SomePartialKnowledge ks ds1 -> SomePartialKnowledge ks ds2 -> SomePartialKnowledge ks (MergedPartialKnowledge ds1 ds2)
instance MergePartialKnowledge 'DZ 'DZ where
    type MergedPartialKnowledge 'DZ 'DZ = 'DZ
    mergePartialKnowledge (SomePartialKnowledge ExplicitPartialKnowledgeNil) (SomePartialKnowledge ExplicitPartialKnowledgeNil) = SomePartialKnowledge ExplicitPartialKnowledgeNil
instance MergePartialKnowledge ds1 ds2 => MergePartialKnowledge ('DS 'Unknown ds1) ('DS 'Unknown ds2) where
    type MergedPartialKnowledge ('DS 'Unknown ds1) ('DS 'Unknown ds2) = 'DS 'Unknown (MergedPartialKnowledge ds1 ds2)
    mergePartialKnowledge (SomePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU ks1)) (SomePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU ks2)) =
        case mergePartialKnowledge (SomePartialKnowledge ks1) (SomePartialKnowledge ks2) of
            SomePartialKnowledge merged -> SomePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU merged)
instance MergePartialKnowledge ds1 ds2 => MergePartialKnowledge ('DS 'Known ds1) ('DS 'Unknown ds2) where
    type MergedPartialKnowledge ('DS 'Known ds1) ('DS 'Unknown ds2) = 'DS 'Known (MergedPartialKnowledge ds1 ds2)
    mergePartialKnowledge (SomePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s) ks1)) (SomePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU ks2)) =
        case mergePartialKnowledge (SomePartialKnowledge ks1) (SomePartialKnowledge ks2) of
            SomePartialKnowledge merged -> SomePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s) merged)
instance MergePartialKnowledge ds1 ds2 => MergePartialKnowledge ('DS 'Unknown ds1) ('DS 'Known ds2) where
    type MergedPartialKnowledge ('DS 'Unknown ds1) ('DS 'Known ds2) = 'DS 'Known (MergedPartialKnowledge ds1 ds2)
    mergePartialKnowledge (SomePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU ks1)) (SomePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s) ks2)) =
        case mergePartialKnowledge (SomePartialKnowledge ks1) (SomePartialKnowledge ks2) of
            SomePartialKnowledge merged -> SomePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s) merged)
instance (SDecide k, MergePartialKnowledge ds1 ds2) => MergePartialKnowledge ('DS 'Known ds1 :: DepStateList (k -> ks)) ('DS 'Known ds2) where
    type MergedPartialKnowledge ('DS 'Known ds1) ('DS 'Known ds2) = 'DS 'Known (MergedPartialKnowledge ds1 ds2)
    mergePartialKnowledge (SomePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s1) ks1)) (SomePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s2) ks2)) =
        case s1 %~ s2 of
            Proved Refl ->
                case mergePartialKnowledge (SomePartialKnowledge ks1) (SomePartialKnowledge ks2) of
                    SomePartialKnowledge merged -> SomePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s1) merged)
            Disproved r -> error "Learned something contradictory"  -- Or: error ("((Sing) Refuted: " ++ show (withSingI (sing @(Interpret (Var VZ) vars)) $ demote @(Interpret (Var VZ) vars)) ++ " %~ " ++ show (withSingI s $ demote @size1) ++ ")")

mergePartiallyKnowns :: MergePartialKnowledge ds1 ds2 => PartiallyKnownK ks f ds1 -> PartiallyKnownK ks g ds2 -> PartiallyKnownK ks (f :*: g) (MergedPartialKnowledge ds1 ds2)
mergePartiallyKnowns (PartiallyKnownK ds1 a) (PartiallyKnownK ds2 b) =
    case mergePartialKnowledge (SomePartialKnowledge ds1) (SomePartialKnowledge ds2) of
        SomePartialKnowledge merged -> PartiallyKnownK merged (unsafeCoerce a :*: unsafeCoerce b)  -- hmmm...


class DepKDeserializeK (f :: LoT ks -> Type) where
    type DepStateRequirements (f :: LoT ks -> Type) (ds :: DepStateList ks) :: Constraint
    type TaughtByK (f :: LoT ks -> Type) :: DepStateList ks
    depKDeserializeK :: DepStateRequirements f ds => ExplicitPartialKnowledge ks xs ds -> [Word8] -> (PartiallyKnownK ks f (TaughtByK f), [Word8])

instance (SingKind k, Serialize (Demote k), AddingVth v) => DepKDeserializeK (Field (Kon (Sing :: k -> Type) :@: Var v)) where
    type DepStateRequirements (Field (Kon (Sing :: k -> Type) :@: Var v)) ds = ()
    type TaughtByK (Field (Kon (Sing :: k -> Type) :@: Var v)) = AddVth 'Known v
    depKDeserializeK _ bs =
        case deserialize bs of
            (FromSing (s :: Sing (s :: k)), bs') ->
                case learnVth @_ @_ @v s of
                    SomePartialKnowledge newKnowledge ->
                        (PartiallyKnownK newKnowledge (Field (unsafeCoerce s)), bs')  -- hmmm...

instance (Serialize t, GettingVth v, FillingUnknowns ks) => DepKDeserializeK (Field (Kon (Vector t :: Nat -> Type) :@: Var (v :: TyVar ks Nat))) where
    type DepStateRequirements (Field (Kon (Vector t :: Nat -> Type) :@: Var (v :: TyVar ks Nat))) ds = GetVthDepState v ds ~ 'Known
    type TaughtByK (Field (Kon (Vector t :: Nat -> Type) :@: Var (v :: TyVar ks Nat))) = FillUnkowns ks
    depKDeserializeK ks bs =
        case knowVth @_ @_ @v (SomePartialKnowledge ks) of
            SomeSing (SNat :: Sing n) ->
                case deserialize @(Vector t n) bs of
                    (a, bs') ->
                        case fillUnkowns of
                            SomePartialKnowledge filled ->
                                (PartiallyKnownK filled (Field (unsafeCoerce a)), bs')  -- hmmm...

instance (DepKDeserializeK l, DepKDeserializeK r, MergePartialKnowledge (TaughtByK l) (TaughtByK r)) => DepKDeserializeK ((l :: LoT ks -> Type) :*: (r :: LoT ks -> Type)) where
    type DepStateRequirements ((l :: LoT ks -> Type) :*: (r :: LoT ks -> Type)) ds =
        ( MergePartialKnowledge ds (TaughtByK l)
        , DepStateRequirements l ds
        , DepStateRequirements r (ds `MergedPartialKnowledge` TaughtByK l)
        )
    type TaughtByK ((l :: LoT ks -> Type) :*: (r :: LoT ks -> Type)) = TaughtByK l `MergedPartialKnowledge` TaughtByK r

    depKDeserializeK (ks :: ExplicitPartialKnowledge ks xs ds) bs =
        case depKDeserializeK @ks @l ks bs of
            (pk1@(PartiallyKnownK (ks' :: ExplicitPartialKnowledge ks xs' (TaughtByK l)) l), bs') ->
                case SomePartialKnowledge ks `mergePartialKnowledge` SomePartialKnowledge ks' of
                    SomePartialKnowledge merged ->
                        case depKDeserializeK @ks @r merged bs' of
                            (pk2@(PartiallyKnownK (ks'' :: ExplicitPartialKnowledge ks xs'' (TaughtByK r)) r), bs'') ->
                                (mergePartiallyKnowns pk1 pk2, bs'')

instance DepKDeserializeK f => DepKDeserializeK (M1 i c f) where
    type DepStateRequirements (M1 i c f) ds = DepStateRequirements f ds
    type TaughtByK (M1 i c f) = TaughtByK f
    depKDeserializeK ks bs =
        case depKDeserializeK ks bs of
            (PartiallyKnownK ks' a, bs') ->
                (PartiallyKnownK ks' (M1 a), bs')


newtype Generic0KWrapper f xs = Generic0KWrapper { unwrapGeneric0K :: Field (Kon f) xs }
instance (DepKDeserializeK (RepK f), GenericK f LoT0, FillingUnknowns ks) => DepKDeserializeK (Generic0KWrapper f :: LoT ks -> Type) where
    type DepStateRequirements (Generic0KWrapper f :: LoT ks -> Type) ds = DepStateRequirements (RepK f) 'DZ
    type TaughtByK (Generic0KWrapper f :: LoT ks -> Type) = FillUnkowns ks
    depKDeserializeK ds bs =
        case depKDeserializeK ExplicitPartialKnowledgeNil bs :: (PartiallyKnownK Type (RepK f) (TaughtByK (RepK f)), [Word8]) of
            (PartiallyKnownK ExplicitPartialKnowledgeNil a, bs') ->
                case fillUnkowns @ks of
                    SomePartialKnowledge learned ->
                        (PartiallyKnownK learned (Generic0KWrapper (Field (unsafeCoerce (toK @_ @f a)))), bs')

newtype Generic1KWrapper f v1 xs = Generic1KWrapper { unwrapGeneric1K :: Field (Kon f :@: Var v1) xs }
type family
    Learn1Vars (v1 :: TyVar ks a1) (ds :: DepStateList (a1 -> Type)) :: DepStateList ks where
    Learn1Vars (v1 :: TyVar ks a1) ('DS d1 'DZ) = AddVth d1 v1
learn1Vars
    :: forall (v1 :: TyVar ks a1) d1.
    (AddingVth v1
    -- TODO: Combinatory explosion.
    )
    => SomePartialKnowledge (a1 -> Type) ('DS d1 'DZ) -> SomePartialKnowledge ks (Learn1Vars v1 ('DS d1 'DZ))
learn1Vars (SomePartialKnowledge (ExplicitPartialKnowledgeCons (k1 :: Knowledge d1 x1) ExplicitPartialKnowledgeNil)) =
    case k1 of
        -- TODO: Combinatory explosion.
        (KnowledgeU) ->       addVth @_ @_ @v1 KnwlgU
        (KnowledgeK s1) ->    addVth @_ @_ @v1 (KnwlgK s1)
instance
    ( DepKDeserializeK (RepK f)
    , forall x1. GenericK f (x1 :&&: LoT0)
    , GettingVth v1
    , AddingVth v1
    )
    => DepKDeserializeK (Generic1KWrapper f (v1 :: TyVar ks a1) :: LoT ks -> Type) where
    type DepStateRequirements (Generic1KWrapper f (v1 :: TyVar ks a1) :: LoT ks -> Type) ds =
        DepStateRequirements (RepK f) ('DS (GetVthDepState v1 ds) 'DZ)
    type TaughtByK (Generic1KWrapper f (v1 :: TyVar ks a1) :: LoT ks -> Type) = Learn1Vars v1 (TaughtByK (RepK f))
    depKDeserializeK ds bs =
        withKnwlg (getVth @_ @_ @v1 (SomePartialKnowledge ds)) $ \k1 ->
            case depKDeserializeK (ExplicitPartialKnowledgeCons k1 ExplicitPartialKnowledgeNil) bs
                    :: (PartiallyKnownK (a1 -> Type) (RepK f) (TaughtByK (RepK f)), [Word8]) of
                (PartiallyKnownK pk@(ExplicitPartialKnowledgeCons (k3 :: Knowledge d1 x1) ExplicitPartialKnowledgeNil) a, bs') ->
                    case learn1Vars @ks @a1 @v1 @d1 (SomePartialKnowledge pk) of
                        SomePartialKnowledge learned ->
                            (PartiallyKnownK learned (Generic1KWrapper (Field (unsafeCoerce (toK @_ @f a)))), bs')

newtype Generic2KWrapper f v1 v2 xs = Generic2KWrapper { unwrapGeneric2K :: Field (Kon f :@: Var v1 :@: Var v2) xs }
type family
    Learn2Vars (v1 :: TyVar ks a1) (v2 :: TyVar ks a2) (ds :: DepStateList (a1 -> a2 -> Type)) :: DepStateList ks where
    Learn2Vars (v1 :: TyVar ks a1) (v2 :: TyVar ks a2) ('DS d1 ('DS d2 'DZ)) = AddVth d1 v1 `MergedPartialKnowledge` AddVth d2 v2
learn2Vars
    :: forall (v1 :: TyVar ks a1) (v2 :: TyVar ks a2) d1 d2.
    (AddingVth v1, AddingVth v2
    -- TODO: Combinatory explosion.
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Known   v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Known   v2)
    )
    => SomePartialKnowledge (a1 -> a2 -> Type) ('DS d1 ('DS d2 'DZ)) -> SomePartialKnowledge ks (Learn2Vars v1 v2 ('DS d1 ('DS d2 'DZ)))
learn2Vars (SomePartialKnowledge (ExplicitPartialKnowledgeCons (k1 :: Knowledge d1 x1) (ExplicitPartialKnowledgeCons (k2 :: Knowledge d2 x2) ExplicitPartialKnowledgeNil))) =
    case (k1, k2) of
        -- TODO: Combinatory explosion.
        (KnowledgeU, KnowledgeU) ->       addVth @_ @_ @v1 KnwlgU      `mergePartialKnowledge` addVth @_ @_ @v2 KnwlgU
        (KnowledgeU, KnowledgeK s2) ->    addVth @_ @_ @v1 KnwlgU      `mergePartialKnowledge` addVth @_ @_ @v2 (KnwlgK s2)
        (KnowledgeK s1, KnowledgeU) ->    addVth @_ @_ @v1 (KnwlgK s1) `mergePartialKnowledge` addVth @_ @_ @v2 KnwlgU
        (KnowledgeK s1, KnowledgeK s2) -> addVth @_ @_ @v1 (KnwlgK s1) `mergePartialKnowledge` addVth @_ @_ @v2 (KnwlgK s2)
instance
    ( DepKDeserializeK (RepK f)
    , forall x1 x2. GenericK f (x1 :&&: x2 :&&: LoT0)
    , GettingVth v1, GettingVth v2
    , AddingVth v1, AddingVth v2
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Unknown v1) (AddVth 'Known   v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Unknown v2)
    , MergePartialKnowledge (AddVth 'Known   v1) (AddVth 'Known   v2)
    )
    => DepKDeserializeK (Generic2KWrapper f (v1 :: TyVar ks a1) (v2 :: TyVar ks a2) :: LoT ks -> Type) where
    type DepStateRequirements (Generic2KWrapper f (v1 :: TyVar ks a1) (v2 :: TyVar ks a2) :: LoT ks -> Type) ds =
        DepStateRequirements (RepK f) ('DS (GetVthDepState v1 ds) ('DS (GetVthDepState v2 ds) 'DZ))
    type TaughtByK (Generic2KWrapper f (v1 :: TyVar ks a1) (v2 :: TyVar ks a2) :: LoT ks -> Type) = Learn2Vars v1 v2 (TaughtByK (RepK f))
    depKDeserializeK ds bs =
        withKnwlg (getVth @_ @_ @v1 (SomePartialKnowledge ds)) $ \k1 ->
            withKnwlg (getVth @_ @_ @v2 (SomePartialKnowledge ds)) $ \k2 ->
                case depKDeserializeK (ExplicitPartialKnowledgeCons k1 (ExplicitPartialKnowledgeCons k2 ExplicitPartialKnowledgeNil)) bs
                        :: (PartiallyKnownK (a1 -> a2 -> Type) (RepK f) (TaughtByK (RepK f)), [Word8]) of
                    (PartiallyKnownK pk@(ExplicitPartialKnowledgeCons (k3 :: Knowledge d1 x1) (ExplicitPartialKnowledgeCons (k4 :: Knowledge d2 x2) ExplicitPartialKnowledgeNil)) a, bs') ->
                        case learn2Vars @ks @a1 @a2 @v1 @v2 @d1 @d2 (SomePartialKnowledge pk) of
                            SomePartialKnowledge learned ->
                                (PartiallyKnownK learned (Generic2KWrapper (Field (unsafeCoerce (toK @_ @f a)))), bs')


--}--}--}--}--}--}

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

module DepKDeserializeV where

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
data PartiallyKnown (f :: ks) (ds :: DepStateList ks) where
    PartiallyKnown :: ExplicitPartialKnowledge ks xs ds -> f :@@: xs -> PartiallyKnown f ds

class DepKDeserializeV (f :: ks) where
    type DepStateReqs (f :: ks) (ds :: DepStateList ks) :: Constraint
    type TaughtBy (f :: ks) :: DepStateList ks
    depKDeserializeV :: DepStateReqs f ds => ExplicitPartialKnowledge ks xs ds -> [Word8] -> (PartiallyKnown f (TaughtBy f), [Word8])
-}


{-
data ExplicitPartialKnowledge (xs :: LoT ks) (ds :: DepStateList ks) where
    ExplicitPartialKnowledgeNil  :: ExplicitPartialKnowledge LoT0 'DZ
    ExplicitPartialKnowledgeCons :: Knowledge d (x :: a) -> ExplicitPartialKnowledge xs ds -> ExplicitPartialKnowledge (x :&&: xs) ('DS d ds)

data SomePartialKnowledge (ds :: DepStateList ks) where
    SomePartialKnowledge :: ExplicitPartialKnowledge xs ds -> SomePartialKnowledge ds

--data PartiallyKnown (f :: LoT ks -> Type) (ds :: DepStateList ks) where
--    PartiallyKnown :: ExplicitPartialKnowledge xs ds -> f xs -> PartiallyKnown f ds

--class DepKDeserializeV (f :: ks) (a :: Atom ls ks) where
--    type DepStateReqs (f :: ks) (a :: Atom ls ks) (ds :: DepStateList ls) :: Constraint
--    type TaughtBy (f :: ks) (a :: Atom ls ks) :: DepStateList ls
--    idunnolol :: forall (x :: ks -> Type) (xs :: LoT ls). Field (Kon x :@: a) xs
--    --depKDeserializeV :: [Word8] -> (f xs, SomePartialKnowledge ?, [Word8])
--
--instance DepKDeserializeV (Sing :: Nat -> Type) (Var3 :: Atom (k0 -> k1 -> k2 -> (Nat -> Type) -> Type) (Nat -> Type))

--_foo :: forall (f :: ks) (a :: Atom ks Type). Int
--_foo = undefined

--class DepKDeserializeA (a :: Atom d ks)
--instance DepKDeserializeA (Kon (Sing :: Nat -> Type) :: Atom d (Nat -> Type))

--class DepKDeserializeA (a :: Atom ks Type)
----instance DepKDeserializeA (Kon (Sing :: Nat -> Type) :@: a0)
--instance DepKDeserializeA (Kon (Sing :: Nat -> Type) :@: Kon k0 :: Atom ks Type)
--instance DepKDeserializeA (Kon (Sing :: Nat -> Type) :@: Var v0 :: Atom ks Type)

--data Foo (a :: Atom d ks) (ds :: DepStateList d) where
--    FooNil :: Foo (Kon f) ds
--    FooCons ::

--data Args (ks :: Type) where
--    ArgsNil :: Args Type
--    ArgsCons :: Atom k Type -> Args ks -> Args (k -> ks)

class DepKDeserialize (f :: ks) where
    type DepLevels (f :: ks) :: DepLevelList ks
    depKDeserialize :: SomePartialKnowledge (ds :: DepStateList d) -> [Word8] -> (Void, [Word8])
instance DepKDeserialize (Sing :: Nat -> Type) where
    type DepLevels (Sing :: Nat -> Type) = DLS Learning DLZ
-}

-- TODO: An idea worth considering: Add a `Phantom` state. Could maybe get rid of unsafeCoerces.
--  But this could be nonsense.
--data DepState = Unknown | Known | Phantom

data DepStateList :: Type -> Type where
    DZ :: DepStateList Type
    DS :: DepState -> DepStateList xs -> DepStateList (x -> xs)

data DepLevelList :: Type -> Type where
    DLZ :: DepLevelList Type
    DLS :: DepLevel -> DepLevelList xs -> DepLevelList (x -> xs)

data AtomList :: Type -> Type -> Type where
    AtomNil  :: AtomList d Type
    AtomCons :: Atom d k -> AtomList d ks -> AtomList d (k -> ks)


data family KnowledgeList :: DepStateList d -> Type
data instance KnowledgeList 'DZ where
    KnowledgeNil :: KnowledgeList 'DZ
data instance KnowledgeList ('DS d ds) where
    KnowledgeCons
        :: Knowledge d (x :: k)
        -> KnowledgeList (ds :: DepStateList ks)
        -> KnowledgeList ('DS d ds :: DepStateList (k -> ks))

data AnyK (f :: ks) where
    AnyZ :: f -> AnyK f
    AnyS :: AnyK (f x) -> AnyK f


class RequireAtom (a :: Atom d k) (ds :: DepStateList d) where
    getAtom :: KnowledgeList ds -> SomeSing k
instance SingI a => RequireAtom ('Kon (a :: k)) ds where
    getAtom _ = SomeSing (sing @a)
instance d ~ 'Known => RequireAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS d ds) where
    getAtom (KnowledgeCons (KnowledgeK s) _) = SomeSing s
instance RequireAtom ('Var v) ds => RequireAtom ('Var ('VS v) :: Atom (i -> ks) k) ('DS d ds) where
    getAtom (KnowledgeCons _ kl) = getAtom @ks @k @('Var v) @ds kl

type family
    LearnAtom (a :: Atom d k) (ds :: DepStateList d) :: DepStateList d where
    LearnAtom ('Kon _) ds = ds
    LearnAtom ('Var  'VZ   ) ('DS _ ds) = 'DS 'Known ds
    LearnAtom ('Var ('VS v)) ('DS d ds) = 'DS d (LearnAtom ('Var v) ds)
class LearnableAtom (a :: Atom d k) (ds :: DepStateList d) where  -- TODO: Bad name.
    -- TODO: `Maybe` to cover "contradiction". is an `Either` or something a better fit?
    learnAtom :: SomeSing k -> KnowledgeList ds -> Maybe (KnowledgeList (LearnAtom a ds))
instance (SingI a, SDecide k) => LearnableAtom ('Kon (a :: k)) ds where
    learnAtom (SomeSing s) kl =
        case s %~ sing @a of
            Proved Refl -> Just kl
            Disproved r -> Nothing
instance SDecide k => LearnableAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS d ds) where
    learnAtom (SomeSing s) (KnowledgeCons KnowledgeU kl) = Just (KnowledgeCons (KnowledgeK s) kl)
    learnAtom (SomeSing s) curr@(KnowledgeCons (KnowledgeK s') kl) =
        case s %~ s' of
            Proved Refl -> Just curr
            Disproved r -> Nothing
instance LearnableAtom ('Var v) ds => LearnableAtom ('Var ('VS v) :: Atom (i -> ks) k) ('DS d ds) where
    learnAtom ss (KnowledgeCons k kl) = KnowledgeCons k <$> learnAtom @ks @k @('Var v) @ds ss kl

-- TODO: Is it sensible that this is indexed by a TyVar and not a Nat?
type family
    AtomAt (n :: TyVar ks k) (as :: AtomList d ks) :: Atom d k where
    AtomAt 'VZ (AtomCons a _) = a
    AtomAt ('VS v) (AtomCons _ as) = AtomAt v as

class DepKDeserialize (f :: ks) where
    type Require (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint
    type Learn (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  Require f as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK f, KnowledgeList (Learn f as ds))

instance (SingKind k, Serialize (Demote k)) => DepKDeserialize (Sing :: k -> Type) where
    type Require (Sing :: k -> Type) as ds = LearnableAtom (AtomAt 'VZ as) ds
    type Learn (Sing :: k -> Type) as ds = LearnAtom (AtomAt 'VZ as) ds

    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (k -> Type))
        .  LearnableAtom (AtomAt 'VZ as) ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK (Sing :: k -> Type), KnowledgeList (Learn (Sing :: k -> Type) as ds))
    depKDeserialize _ kl = do
        d <- state deserialize
        case d of
            FromSing (s :: Sing (s :: k)) ->
                case learnAtom @d @k @(AtomAt 'VZ as) (SomeSing s) kl of
                    Nothing -> error "Learned something contradictory"
                    Just kl' ->
                        return (AnyS (AnyZ s), kl')

instance Serialize a => DepKDeserialize (Vector a :: Nat -> Type) where
    type Require (Vector a :: Nat -> Type) as ds = RequireAtom (AtomAt 'VZ as) ds
    type Learn (Vector a :: Nat -> Type) _ ds = ds

    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Nat -> Type))
        .  RequireAtom (AtomAt 'VZ as) ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK (Vector a :: Nat -> Type), KnowledgeList (Learn (Vector a :: Nat -> Type) as ds))
    depKDeserialize _ kl =
        case getAtom @d @Nat @(AtomAt 'VZ as) @ds kl of
            SomeSing (SNat :: Sing n) -> do
                (a :: Vector a n) <- state deserialize
                return (AnyS (AnyZ a), kl)


data AnyKK :: (LoT ks -> Type) -> Type where
    AnyKK :: f xs -> AnyKK f

class DepKDeserializeK (f :: LoT ks -> Type) where
    type RequireK (f :: LoT ks -> Type) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint
    type LearnK (f :: LoT ks -> Type) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d
    depKDeserializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  RequireK f as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyKK f, KnowledgeList (LearnK f as ds))

-- TODO: Write wappers around these where `t` is pinned to kind (Atom d Type)?
type family
    AtomKonKind (t :: Atom ks k) :: Type where
    AtomKonKind ('Kon (f :: k)) = k
    AtomKonKind (t :@: _) = AtomKonKind t

type family
    AtomKonConstructor (t :: Atom ks k) :: AtomKonKind t where
    AtomKonConstructor ('Kon (f :: k)) = f
    AtomKonConstructor (t :@: _) = AtomKonConstructor t

type family
    AtomKonAtomListStep (t :: Atom ks k) (as :: AtomList ks acc) :: AtomList ks (AtomKonKind t) where
    AtomKonAtomListStep ('Kon (f :: k)) as = as
    AtomKonAtomListStep (t :@: a) as = AtomKonAtomListStep t ('AtomCons a as)
type family
    AtomKonAtomList (t :: Atom ks k) :: AtomList ks (AtomKonKind t) where
    AtomKonAtomList t = AtomKonAtomListStep t 'AtomNil

-- TODO: Here be dragons. If this is actually part of a solution, I should better form an understanding around this part.
type family
    DereferenceAtom (base :: AtomList d ks) (a :: Atom ks k) :: Atom d k where
    DereferenceAtom _ ('Kon a) = 'Kon a
    DereferenceAtom as ('Var v) = AtomAt v as
type family
    DereferenceAtomList (base :: AtomList d ks) (as :: AtomList ks ks') :: AtomList d ks' where
    DereferenceAtomList _ 'AtomNil = 'AtomNil
    DereferenceAtomList base ('AtomCons a as) = 'AtomCons (DereferenceAtom base a) (DereferenceAtomList base as)

unsafeExtractAnyK :: forall ks (f :: ks) (xs :: LoT ks). AnyK f -> f :@@: xs
unsafeExtractAnyK = undefined

instance (DepKDeserialize (AtomKonConstructor t)) => DepKDeserializeK (Field t :: LoT ks -> Type) where
    type RequireK (Field t :: LoT ks -> Type) (as :: AtomList d ks) (ds :: DepStateList d) =
        Require (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds
    type LearnK (Field t :: LoT ks -> Type) (as :: AtomList d ks)  (ds :: DepStateList d) =
        Learn (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds

    depKDeserializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  RequireK (Field t :: LoT ks -> Type) as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyKK (Field t :: LoT ks -> Type), KnowledgeList (LearnK (Field t :: LoT ks -> Type) as ds))
    depKDeserializeK _ kl = do
        (anykf, kl') <- depKDeserialize @(AtomKonKind t) @(AtomKonConstructor t) (Proxy @(DereferenceAtomList as (AtomKonAtomList t))) kl
        return (AnyKK (Field (unsafeCoerce (unsafeExtractAnyK @(AtomKonKind t) @(AtomKonConstructor t) anykf))), kl')

instance (DepKDeserializeK f, DepKDeserializeK g) => DepKDeserializeK (f :*: g :: LoT ks -> Type) where
    type RequireK (f :*: g :: LoT ks -> Type) as ds =
        ( RequireK f as ds
        , RequireK g as (LearnK f as ds)
        )
    type LearnK (f :*: g :: LoT ks -> Type) as ds = LearnK g as (LearnK f as ds)
    depKDeserializeK p kl = do
        (AnyKK a, kl') <- depKDeserializeK @ks @f p kl
        (AnyKK a', kl'') <- depKDeserializeK @ks @g p kl'
        return (AnyKK (unsafeCoerce a :*: a'), kl'')  -- TODO: Would be excellent to get rid of unsafeCoerce!

instance DepKDeserializeK f => DepKDeserializeK (M1 i c f :: LoT ks -> Type) where
    type RequireK (M1 i c f) as ds = RequireK f as ds
    type LearnK (M1 i c f) as ds = LearnK f as ds
    depKDeserializeK p kl = do
        (AnyKK a, kl') <- depKDeserializeK @ks @f p kl
        return (AnyKK (M1 a), kl')


---- TODO: Should be some recursive way to do this too, right? A data family perhaps?
--newtype GenericKWrapper0 f = GenericKWrapper0 f
--instance DepKDeserializeK (RepK f) => DepKDeserialize (GenericKWrapper0 f) where
--    type Require (GenericKWrapper0 f) 'AtomNil ds = RequireK (Field ('Kon f)) ds
--    type Learn (GenericKWrapper0 f) 'AtomNil ds = LearnK (Field ('Kon f)) ds
--    --depKDeserialize _ kl = do
--    --    (_, kl') <- depKDeserializeK @Type @(Field ('Kon f)) kl
--    --    return (undefined, kl')
--newtype GenericKWrapper1 f x0 = GenericKWrapper1 (f x0)
--instance DepKDeserializeK (RepK f) => DepKDeserialize (GenericKWrapper1 f) where
--    type Require (GenericKWrapper1 f) ('AtomCons a0 'AtomNil) ds = RequireK (Field ('Kon f :@: a0)) ds
--    type Learn (GenericKWrapper1 f) ('AtomCons a0 'AtomNil) ds = LearnK (Field ('Kon f :@: a0)) ds
--    --depKDeserialize _ kl = do
--    --    (_, kl') <- depKDeserializeK @Type @(Field ('Kon f)) kl
--    --    return (undefined, kl')
newtype GenericKWrapper2 f x0 x1 = GenericKWrapper2 (f x0 x1)
    deriving (Show)
instance (forall size0 size1. GenericK f (size0 :&&: size1 :&&: 'LoT0), DepKDeserializeK (RepK f)) => DepKDeserialize (GenericKWrapper2 f :: k0 -> k1 -> Type) where
    type Require (GenericKWrapper2 f) as ds = RequireK (RepK f) as ds
    type Learn (GenericKWrapper2 f) as ds = LearnK (RepK f) as ds
    depKDeserialize p kl = do
        (AnyKK (r :: RepK f xs), kl') <- depKDeserializeK @(k0 -> k1 -> Type) @(RepK f) p kl
        -- TODO: What is this even?
        case unsafeCoerce (Refl :: xs :~: xs) :: xs :~: (size0 :&&: size1 :&&: 'LoT0) of
            Refl -> return (AnyS (AnyS (AnyZ (GenericKWrapper2 (unsafeCoerce (toK @_ @f r))))), kl')


data L0R1 (size0 :: Nat) (size1 :: Nat) = L0R1
    { size0 :: Sing size0
    , arr1  :: Vector Word8 size1
    } deriving (Show, GHC.Generic)
$(deriveGenericK 'L0R1)
--deriving via GenericKWrapper2 L0R1 instance DepKDeserialize L0R1

--instance DepKDeserialize (L0R1 :: Nat -> Nat -> Type) where
--    type Require (L0R1 :: Nat -> Nat -> Type) as ds =
--        ( LearnableAtom (AtomAt 'VZ as) ds
--        , RequireAtom (AtomAt ('VS 'VZ) as) (LearnAtom (AtomAt 'VZ as) ds)
--        )
--    type Learn (L0R1 :: Nat -> Nat -> Type) as ds = LearnAtom (AtomAt 'VZ as) ds
--    depKDeserialize (Proxy :: Proxy as) kl = do
--        (AnyS (AnyZ size0), kl') <- depKDeserialize @(Nat -> Type) @Sing (Proxy @(AtomCons (AtomAt 'VZ as) AtomNil)) kl
--        (AnyS (AnyZ arr1), kl'') <- depKDeserialize @(Nat -> Type) @(Vector Word8) (Proxy @(AtomCons (AtomAt ('VS 'VZ) as) AtomNil)) kl'
--        return (AnyS (AnyS (AnyZ (L0R1 size0 arr1))), kl'')

-- TODO: I've rewritten these in terms of (GenericKWrapper2 L0R1) instead of L0R1.
--  Shouldn't really have to do that. I can write the (DepKDeserialize (L0R1)) instance by hand,
--  but I want a way to derive it, and I haven't quite gottn there yet.
testL0R1SameVar :: String
testL0R1SameVar =
    case evalState
            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyS (AnyS (AnyZ a)), _) -> show a

testL0R1DifferentVars :: String
testL0R1DifferentVars =
    case evalState
            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))) (KnowledgeCons KnowledgeU (KnowledgeCons (KnowledgeK (sing @5)) KnowledgeNil)))
            [2,3,4,5,6,7] of
        (AnyS (AnyS (AnyZ a)), _) -> show a

testL0R1Kons :: String
testL0R1Kons =
    case evalState
            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons ('Kon 2) (AtomCons ('Kon 5) AtomNil))) KnowledgeNil)
            [2,3,4,5,6,7] of
        (AnyS (AnyS (AnyZ a)), _) -> show a

testL0R1KonsContradictory :: String
testL0R1KonsContradictory =
    case evalState
            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons ('Kon 1) (AtomCons ('Kon 5) AtomNil))) KnowledgeNil)
            [2,3,4,5,6,7] of
        (AnyS (AnyS (AnyZ a)), _) -> show a

testL0R1AlreadyKnown :: String
testL0R1AlreadyKnown =
    case evalState
            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))) (KnowledgeCons (KnowledgeK (sing @2)) KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyS (AnyS (AnyZ a)), _) -> show a


testL0R1AlreadyKnownContradictory :: String
testL0R1AlreadyKnownContradictory =
    case evalState
            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))) (KnowledgeCons (KnowledgeK (sing @1)) KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyS (AnyS (AnyZ a)), _) -> show a

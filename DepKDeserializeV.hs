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

--type role AnyK representational
--data AnyK (f :: ks) where
--    AnyZ :: a -> AnyK a
--    AnyS :: Proxy x -> f x -> AnyK f
data AnyK (f :: ks) where
    AnyK :: Proxy xs -> f :@@: xs -> AnyK f


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
instance LearnableAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS 'Unknown ds) where
    learnAtom (SomeSing s) (KnowledgeCons KnowledgeU kl) = Just (KnowledgeCons (KnowledgeK s) kl)
instance SDecide k => LearnableAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS 'Known ds) where
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

-- TODO: This is pretty weird... I'm surprised that this workaround works. If indeed it really always does...
type family
    Tail (xs :: LoT (k -> ks)) :: LoT ks where
    Tail (x :&&: xs) = xs
type family
    InterpretVars (xs :: LoT ks) :: LoT ks where
    InterpretVars (xs :: LoT Type) = 'LoT0
    InterpretVars (xs :: LoT (k -> ks)) = InterpretVar 'VZ xs :&&: InterpretVars (Tail xs)
interpretVarsIsJustVars :: forall xs. Dict (InterpretVars xs ~ xs)
interpretVarsIsJustVars = unsafeCoerce (Dict @(xs ~ xs))
class GenericK f (InterpretVars xs) => GenericK' (f :: ks) (xs :: LoT ks)
instance GenericK f (InterpretVars xs) => GenericK' (f :: ks) (xs :: LoT ks)
genericKInstance :: forall f xs. GenericK' f xs :- GenericK f xs
genericKInstance = Sub (withDict (interpretVarsIsJustVars @xs) Dict)

class DepKDeserialize (f :: ks) where
    type Require (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint
    type Learn (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  Require f as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK f, KnowledgeList (Learn f as ds))

    -- TODO: I was going for a DerivingVia design rather than default signatures, but that had problems.
    type Require (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) = RequireK (RepK f) as ds
    type Learn (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) = LearnK (RepK f) as ds
    default depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  (forall xs. GenericK' f xs, DepKDeserializeK (RepK f), RequireK (RepK f) as ds, Learn f as ds ~ LearnK (RepK f) as ds)
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK f, KnowledgeList (Learn f as ds))
    depKDeserialize p kl = do
        (AnyKK (r :: RepK f xs), kl') <- depKDeserializeK @_ @(RepK f) p kl
        return (AnyK (Proxy @xs) (toK @_ @f r \\ genericKInstance @f @xs), kl')

instance (SingKind k, Serialize (Demote k)) => DepKDeserialize (Sing :: k -> Type) where
    type Require (Sing :: k -> Type) as ds = LearnableAtom (AtomAt 'VZ as) ds
    type Learn (Sing :: k -> Type) as ds = LearnAtom (AtomAt 'VZ as) ds

    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (k -> Type))
        .  Require (Sing :: k -> Type) as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK (Sing :: k -> Type), KnowledgeList (Learn (Sing :: k -> Type) as ds))
    depKDeserialize _ kl = do
        d <- state deserialize
        case d of
            FromSing (s :: Sing (s :: k)) ->
                case learnAtom @d @k @(AtomAt 'VZ as) (SomeSing s) kl of
                    Nothing -> error "Learned something contradictory"
                    Just kl' ->
                        return (AnyK (Proxy @(s :&&: 'LoT0)) s, kl')

instance (SingKind k, Serialize (Demote k), SDecide k, SingI a) => DepKDeserialize (Sing (a :: k)) where
    type Require (Sing (a :: k)) as ds = ()
    type Learn (Sing (a :: k)) _ ds = ds

    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d Type)
        .  Require (Sing (a :: k)) as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK (Sing (a :: k)), KnowledgeList (Learn (Sing (a :: k)) as ds))
    depKDeserialize _ kl = do
        d <- state deserialize
        case d of
            FromSing (s :: Sing (s :: k)) ->
                case s %~ (sing @a) of
                    Disproved f ->
                        -- TODO: Can we show the expected and actual values?
                        --  A Show instance would be intrusive though. Maybe just show the bytes?
                        error "Deserialized a specified Sing and got another value than specified"
                    Proved Refl -> return (AnyK (Proxy @'LoT0) s, kl)

instance Serialize a => DepKDeserialize (Vector a :: Nat -> Type) where
    type Require (Vector a :: Nat -> Type) as ds = RequireAtom (AtomAt 'VZ as) ds
    type Learn (Vector a :: Nat -> Type) _ ds = ds

    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Nat -> Type))
        .  Require (Vector a :: Nat -> Type) as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK (Vector a :: Nat -> Type), KnowledgeList (Learn (Vector a :: Nat -> Type) as ds))
    depKDeserialize _ kl =
        case getAtom @d @Nat @(AtomAt 'VZ as) @ds kl of
            SomeSing (SNat :: Sing n) -> do
                (a :: Vector a n) <- state deserialize
                return (AnyK (Proxy @(n :&&: 'LoT0)) a, kl)

instance (Serialize a, SingI n) => DepKDeserialize (Vector a n) where
    type Require (Vector a n) as ds = ()
    type Learn (Vector a n) _ ds = ds

    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d Type)
        .  Require (Vector a n) as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK (Vector a n), KnowledgeList (Learn (Vector a n) as ds))
    depKDeserialize _ kl = do
        (a :: Vector a n) <- state deserialize
        return (AnyK (Proxy @'LoT0) a, kl)


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
        (AnyK Proxy a, kl') <- depKDeserialize @(AtomKonKind t) @(AtomKonConstructor t) (Proxy @(DereferenceAtomList as (AtomKonAtomList t))) kl
        return (AnyKK (Field (unsafeCoerce a)), kl')

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


--newtype GenericKWrapper2 f x0 x1 = GenericKWrapper2 (f x0 x1)
--    deriving (Show)
--instance (forall size0 size1. GenericK f (size0 :&&: size1 :&&: 'LoT0), DepKDeserializeK (RepK f)) => DepKDeserialize (GenericKWrapper2 f :: k0 -> k1 -> Type) where
--    type Require (GenericKWrapper2 f) as ds = RequireK (RepK f) as ds
--    type Learn (GenericKWrapper2 f) as ds = LearnK (RepK f) as ds
--    depKDeserialize p kl = do
--        (AnyKK (r :: RepK f xs), kl') <- depKDeserializeK @(k0 -> k1 -> Type) @(RepK f) p kl
--        -- TODO: What is this even?
--        case unsafeCoerce (Refl :: xs :~: xs) :: xs :~: (size0 :&&: size1 :&&: 'LoT0) of
--            Refl -> return (AnyK Proxy (unsafeCoerce (GenericKWrapper2 (unsafeCoerce (toK @_ @f r)))), kl')  -- TODO: Ugghhh...

--instance DepKDeserialize L0R1 where
--    type Require L0R1 as ds = RequireK (RepK L0R1) as ds
--    type Learn L0R1 as ds = LearnK (RepK L0R1) as ds
--    depKDeserialize p kl = do
--        (AnyKK (r :: RepK L0R1 xs), kl') <- depKDeserializeK @(Nat -> Nat -> Type) @(RepK L0R1) p kl
--        return (AnyK (Proxy @xs) (withDict (simply2Vars @_ @_ @L0R1 @xs) (toK @_ @L0R1 r)), kl')

simply0Vars :: forall f (xs :: LoT Type). Dict (xs ~ 'LoT0)
simply0Vars = unsafeCoerce (Dict @(xs ~ xs))  -- TODO: Not sure if correct. And just a hack anyway.

simply1Vars :: forall f (xs :: LoT (k0 -> Type)). Dict (xs ~ (Interpret (Var 'VZ) xs :&&: 'LoT0))
simply1Vars = unsafeCoerce (Dict @(xs ~ xs))  -- TODO: Not sure if correct. And just a hack anyway.

simply2Vars :: forall f (xs :: LoT (k0 -> k1 -> Type)). Dict (xs ~ (Interpret (Var 'VZ) xs :&&: Interpret (Var ('VS 'VZ)) xs :&&: 'LoT0))
simply2Vars = unsafeCoerce (Dict @(xs ~ xs))  -- TODO: Not sure if correct. And just a hack anyway.

---- TODO: I've rewritten these in terms of (GenericKWrapper2 L0R1) instead of L0R1.
----  Shouldn't really have to do that. I can write the (DepKDeserialize (L0R1)) instance by hand,
----  but I want a way to derive it, and I haven't quite gottn there yet.
--testL0R1SameVar :: String
--testL0R1SameVar =
--    case evalState
--            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))) (KnowledgeCons KnowledgeU KnowledgeNil))
--            [2,3,4,5,6,7] of
--        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (simply2Vars @_ @_ @(GenericKWrapper2 L0R1) @xs) $ show a
--
--testL0R1DifferentVars :: String
--testL0R1DifferentVars =
--    case evalState
--            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))) (KnowledgeCons KnowledgeU (KnowledgeCons (KnowledgeK (sing @5)) KnowledgeNil)))
--            [2,3,4,5,6,7] of
--        (AnyK Proxy a, _) -> show a
--
--testL0R1Kons :: String
--testL0R1Kons =
--    case evalState
--            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons ('Kon 2) (AtomCons ('Kon 5) AtomNil))) KnowledgeNil)
--            [2,3,4,5,6,7] of
--        (AnyK Proxy a, _) -> show a
--
--testL0R1KonsContradictory :: String
--testL0R1KonsContradictory =
--    case evalState
--            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons ('Kon 1) (AtomCons ('Kon 5) AtomNil))) KnowledgeNil)
--            [2,3,4,5,6,7] of
--        (AnyK Proxy a, _) -> show a
--
--testL0R1AlreadyKnown :: String
--testL0R1AlreadyKnown =
--    case evalState
--            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))) (KnowledgeCons (KnowledgeK (sing @2)) KnowledgeNil))
--            [2,3,4,5,6,7] of
--        (AnyK Proxy a, _) -> show a
--
--
--testL0R1AlreadyKnownContradictory :: String
--testL0R1AlreadyKnownContradictory =
--    case evalState
--            (depKDeserialize @_ @(GenericKWrapper2 L0R1) (Proxy @(AtomCons Var0 (AtomCons ('Kon 5) AtomNil))) (KnowledgeCons (KnowledgeK (sing @1)) KnowledgeNil))
--            [2,3,4,5,6,7] of
--        (AnyK Proxy a, _) -> show a

newtype GenericKWrapper2 f x0 x1 = GenericKWrapper2 (f x0 x1)
    deriving (Show)
instance ((forall x0 x1. GenericK f (x0 :&&: x1 :&&: 'LoT0)), DepKDeserializeK (RepK f)) => DepKDeserialize (GenericKWrapper2 f :: k0 -> k1 -> Type) where
    type Require (GenericKWrapper2 f) as ds = RequireK (RepK f) as ds
    type Learn (GenericKWrapper2 f) as ds = LearnK (RepK f) as ds
    depKDeserialize p kl = do
        (AnyKK (r :: RepK f xs), kl') <- depKDeserializeK @(k0 -> k1 -> Type) @(RepK f) p kl
        return (AnyK (Proxy @xs) (withDict (simply2Vars @_ @_ @f @xs) (GenericKWrapper2 (toK @_ @f r))), kl')

data L0R1 (size0 :: Nat) (size1 :: Nat) = L0R1
    { size0 :: Sing size0
    , arr1  :: Vector Word8 size1
    } deriving (Show, GHC.Generic)
-- $(deriveGenericK 'L0R1)  -- BUG: Usage of this with e.g. GenericKWrapper2 causes GHC to hang!
instance GenericK L0R1 (size0 :&&: size1 :&&: 'LoT0) where
    type RepK L0R1 = Field (Sing :$: Var0) :*: Field (Vector Word8 :$: Var1)
instance GenericK (L0R1 size0) (size1 :&&: 'LoT0) where
    type RepK (L0R1 size0) = Field ('Kon (Sing size0)) :*: Field (Vector Word8 :$: Var0)
instance GenericK (L0R1 size0 size1) 'LoT0 where
    type RepK (L0R1 size0 size1) = Field ('Kon (Sing size0)) :*: Field ('Kon (Vector Word8 size1))

--deriving via GenericKWrapper2 L0R1 instance DepKDeserialize L0R1
deriving instance DepKDeserialize L0R1
deriving instance SingI size0 => DepKDeserialize (L0R1 size0)
deriving instance (SingI size0, SingI size1) => DepKDeserialize (L0R1 size0 size1)


testL0R1SameVarK :: String
testL0R1SameVarK =
    case evalState
            (depKDeserializeK @_ @(Field (Sing :$: Var0) :*: Field (Vector Word8 :$: Var1)) (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyKK a, _) -> show a

testL0R1SameVar :: String
testL0R1SameVar =
    case evalState
            (depKDeserialize @_ @L0R1 (Proxy @(AtomCons Var0 (AtomCons Var0 AtomNil))) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (simply2Vars @_ @_ @L0R1 @xs) $ show a

testL0R1Of2AndKnown3 :: String
testL0R1Of2AndKnown3 =
    case evalState
            (depKDeserialize @_ @(L0R1 2) (Proxy @(AtomCons Var0 AtomNil)) (KnowledgeCons (KnowledgeK (sing @3)) KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (simply1Vars @_ @L0R1 @xs) show a

testL0R1Of2And3 :: String
testL0R1Of2And3 =
    case evalState
            (depKDeserialize @_ @(L0R1 2 3) (Proxy @AtomNil) KnowledgeNil)
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (simply0Vars @L0R1 @xs) show a

data SameVarL0R1 size = SameVarL0R1
    { l0r1 :: L0R1 size size
    } deriving (Show, GHC.Generic)
-- $(deriveGenericK 'SameVarL0R1)  -- BUG: OK, no GenericKWrapper2 this time. These 3 lines also make it hang.
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

data SameExistentialVarL0R1 =
    forall size. SameExistentialVarL0R1
    { l0r1 :: L0R1 size size
    }
deriving instance Show SameExistentialVarL0R1
instance GenericK SameExistentialVarL0R1 'LoT0 where
    type RepK SameExistentialVarL0R1 = Exists Nat (Field (L0R1 :$: Var0 :@: Var0))
    fromK (SameExistentialVarL0R1 a) = Exists (Field a)
    toK (Exists (Field a)) = SameExistentialVarL0R1 a

deriving instance DepKDeserialize SameExistentialVarL0R1

type family
    IncrVar k (t :: Atom d a) :: Atom (k -> d) a where
    IncrVar _ ('Kon a) = 'Kon a
    IncrVar _ ('Var v) = 'Var ('VS v)
type family
    IncrVars k ks (as :: AtomList d ks) :: AtomList (k -> d) ks where
    IncrVars k Type 'AtomNil = 'AtomNil
    IncrVars k (k' -> ks) ('AtomCons t as) = 'AtomCons (IncrVar k t) (IncrVars k ks as)
type family
    IntroduceTyVar k ks (as :: AtomList d ks) :: AtomList (k -> d) (k -> ks) where
    IntroduceTyVar k ks as = 'AtomCons Var0 (IncrVars k ks as)
type family
    DiscardTyVar (ds :: DepStateList (k -> d)) :: DepStateList d where
    DiscardTyVar ('DS _ ds) = ds
instance DepKDeserializeK f => DepKDeserializeK (Exists k (f :: LoT (k -> ks) -> Type)) where
    type RequireK (Exists k (f :: LoT (k -> ks) -> Type)) as ds = RequireK f (IntroduceTyVar k ks as) ('DS 'Unknown ds)
    type LearnK (Exists k (f :: LoT (k -> ks) -> Type)) as ds = DiscardTyVar (LearnK f (IntroduceTyVar k ks as) ('DS 'Unknown ds))
    depKDeserializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  RequireK (Exists k (f :: LoT (k -> ks) -> Type)) as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyKK (Exists k (f :: LoT (k -> ks) -> Type)), KnowledgeList (LearnK (Exists k (f :: LoT (k -> ks) -> Type)) as ds))
    depKDeserializeK Proxy kl = do
        (AnyKK a, kl') <- depKDeserializeK @_ @f (Proxy :: Proxy (IntroduceTyVar k ks as)) (KnowledgeCons KnowledgeU kl)
        case
            unsafeCoerce  -- TODO: If this is sound and there's no other way, at least factor this out into something general and safe.
                (Refl :: LearnK f (IntroduceTyVar k ks as) ('DS 'Unknown ds) :~: LearnK f (IntroduceTyVar k ks as) ('DS 'Unknown ds))
                      :: LearnK f (IntroduceTyVar k ks as) ('DS 'Unknown ds) :~: 'DS something ds of
            Refl ->
                case kl' of
                    KnowledgeCons _ kl'' ->
                        return (AnyKK (Exists (unsafeCoerce a)), kl'')

testSameExistentialVarL0R1 :: String
testSameExistentialVarL0R1 =
    case evalState
            (depKDeserialize @_ @SameExistentialVarL0R1 (Proxy @AtomNil) KnowledgeNil)
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

{-
-- Example of the flow of atoms between depKDeserialize and depKDeserializeK.

depKDeserialize @(Nat -> Type) @Foo
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

type family Promote (a :: Type) = (b :: Type) | b -> a

-- TODO: Could be more sane to put newtype wrappers around these
--  (maybe make Promote a data family instead?), because this mapping
--  in the Demote direction is arbitrary-looking. Like, why is
--  Demote (Fin 256) = Word8, of all things? Maybe there's some general
--  Demote (Fin n) thing that we could have? There's Natural for Nat,
--  so perhaps a Finite type?
type instance Promote Word8 = Fin 256
type instance Promote Word16 = Fin 65536
type instance Promote Word32 = Fin 4294967296
type instance Promote Word64 = Fin 18446744073709551616

instance SingKind (Fin 256) where
    type Demote (Fin 256) = Word8
    fromSing (SFin :: Sing a) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin 256. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SFin :: Sing a)

instance SingKind (Fin 65536) where
    type Demote (Fin 65536) = Word16
    fromSing (SFin :: Sing a) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin 65536. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SFin :: Sing a)

instance SingKind (Fin 4294967296) where
    type Demote (Fin 4294967296) = Word32
    fromSing (SFin :: Sing a) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin 4294967296. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SFin :: Sing a)

instance SingKind (Fin 18446744073709551616) where
    type Demote (Fin 18446744073709551616) = Word64
    fromSing (SFin :: Sing a) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin 18446744073709551616. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SFin :: Sing a)


data L0Word8 (size :: Fin 256) = L0Word8
    { size :: Sing size
    } deriving (Show, GHC.Generic)
instance GenericK L0Word8 (size :&&: 'LoT0) where
    type RepK L0Word8 = Field (Sing :$: Var0)
instance GenericK (L0Word8 size) 'LoT0 where
    type RepK (L0Word8 size) = Field ('Kon (Sing size))
deriving instance DepKDeserialize L0Word8

testL0Word8 :: String
testL0Word8 =
    case evalState
            (depKDeserialize @_ @L0Word8 (Proxy @('AtomCons Var0 'AtomNil)) (KnowledgeCons KnowledgeU KnowledgeNil))
            [2,3,4,5,6,7] of
        (AnyK (Proxy :: Proxy xs) a, _) -> withDict (interpretVarsIsJustVars @xs) $ show a

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


data DepStateList :: Type -> Type where
    DZ :: DepStateList Type
    DS :: DepState -> DepStateList xs -> DepStateList (x -> xs)

data DepLevelList :: Type -> Type where
    DLZ :: DepLevelList Type
    DLS :: DepLevel -> DepLevelList xs -> DepLevelList (x -> xs)

data AtomList :: Type -> Type -> Type where
    AtomNil  :: AtomList d Type
    AtomCons :: Atom d k -> AtomList d ks -> AtomList d (k -> ks)

data KnowledgeList (ds :: DepStateList d) where
    KnowledgeNil :: KnowledgeList 'DZ
    KnowledgeCons
        :: Knowledge d (x :: k)
        -> KnowledgeList (ds :: DepStateList ks)
        -> KnowledgeList ('DS d ds :: DepStateList (k -> ks))


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


data AnyK (f :: ks) where
    AnyK :: Proxy xs -> f :@@: xs -> AnyK f

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

-- TODO: Is it sensible that this is indexed by a TyVar and not a Nat?
type family
    AtomAt (n :: TyVar ks k) (as :: AtomList d ks) :: Atom d k where
    AtomAt 'VZ (AtomCons a _) = a
    AtomAt ('VS v) (AtomCons _ as) = AtomAt v as

instance Serialize a => DepKDeserialize (Vector a) where
    type Require (Vector a) as ds = RequireAtom (AtomAt 'VZ as) ds
    type Learn (Vector a) _ ds = ds

    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Nat -> Type))
        .  Require (Vector a) as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyK (Vector a), KnowledgeList (Learn (Vector a) as ds))
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

instance (DepKDeserialize (AtomKonConstructor t)) => DepKDeserializeK (Field t) where
    type RequireK (Field t) as (ds :: DepStateList d) =
        Require (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds
    type LearnK (Field t) as (ds :: DepStateList d) =
        Learn (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds

    depKDeserializeK
        :: forall d (ds :: DepStateList d) as
        .  RequireK (Field t) as ds
        => Proxy as -> KnowledgeList ds -> State [Word8] (AnyKK (Field t), KnowledgeList (LearnK (Field t) as ds))
    depKDeserializeK _ kl = do
        (AnyK Proxy a, kl') <- depKDeserialize @(AtomKonKind t) @(AtomKonConstructor t) (Proxy @(DereferenceAtomList as (AtomKonAtomList t))) kl
        return (AnyKK (Field (unsafeCoerce a)), kl')

instance (DepKDeserializeK f, DepKDeserializeK g) => DepKDeserializeK (f :*: g) where
    type RequireK (f :*: g) as ds =
        ( RequireK f as ds
        , RequireK g as (LearnK f as ds)
        )
    type LearnK (f :*: g) as ds = LearnK g as (LearnK f as ds)
    depKDeserializeK p kl = do
        (AnyKK a, kl') <- depKDeserializeK @_ @f p kl
        (AnyKK a', kl'') <- depKDeserializeK @_ @g p kl'
        return (AnyKK (unsafeCoerce a :*: a'), kl'')  -- TODO: Would be excellent to get rid of unsafeCoerce!

instance DepKDeserializeK f => DepKDeserializeK (M1 i c f) where
    type RequireK (M1 i c f) as ds = RequireK f as ds
    type LearnK (M1 i c f) as ds = LearnK f as ds
    depKDeserializeK p kl = do
        (AnyKK a, kl') <- depKDeserializeK @_ @f p kl
        return (AnyKK (M1 a), kl')


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


dep0Deserialize :: forall a. (DepKDeserialize a, Require a 'AtomNil 'DZ) => State [Word8] a
dep0Deserialize = do
    (AnyK (Proxy :: Proxy xs) a, _) <- depKDeserialize @Type @a (Proxy @AtomNil) KnowledgeNil
    return (withDict (interpretVarsIsJustVars @xs) a)


-- NOTE: I don't love the repetitiveness of the type family approach below.
--  I tried a data family like in this comment, but apparently data family instance
--  constructors simply never promote to the kind level... GHC's user guide says it
--  would require full dependent types. I'm not sure why.
--data family Promote (a :: Type)
--
--newtype instance Promote Word8 = PWord8 (Fin 256)
--newtype instance Promote Word16 = PWord16 (Fin 65536)
--newtype instance Promote Word32 = PWord32 (Fin 4294967296)
--newtype instance Promote Word64 = PWord64 (Fin 18446744073709551616)

newtype PWord8 = PWord8 (Fin 256)
newtype PWord16 = PWord16 (Fin 65536)
newtype PWord32 = PWord32 (Fin 4294967296)
newtype PWord64 = PWord64 (Fin 18446744073709551616)

-- NOTE: Also, it turns out that there are no uses for this type family either.
--  Basically it seems I have to use concrete stand-alone types like PWord8 directly.
--  I could use types like Fin 256 directly too and say Demote (Fin 256) = Word8,
--  but I find that a somewhat arbitrary mapping, hence these newtype wrappers.
--type family Promote (a :: Type) = (b :: Type) | b -> a
--
--type instance Promote Word8 = PWord8
--type instance Promote Word16 = PWord16
--type instance Promote Word32 = PWord32
--type instance Promote Word64 = PWord64
--
-- TODO: Potentially, we can explore other approaches than the `Sing (a :: Promote Word8)`
--  that I had imagined, by not trying to make something that can be wrapped in a sing.
--  For example, what if instead of `Sing (a :: Promote Word8)`, we try to make
--  something like `PromotedSing (a :: Word8)` work?

data instance Sing :: PWord8 -> Type where
    SWord8 :: forall (a :: Fin 256). Sing a -> Sing ('PWord8 a)
data instance Sing :: PWord16 -> Type where
    SWord16 :: forall (a :: Fin 65536). Sing a -> Sing ('PWord16 a)
data instance Sing :: PWord32 -> Type where
    SWord32 :: forall (a :: Fin 4294967296). Sing a -> Sing ('PWord32 a)
data instance Sing :: PWord64 -> Type where
    SWord64 :: forall (a :: Fin 18446744073709551616). Sing a -> Sing ('PWord64 a)

instance Show (Sing (a :: PWord8)) where
    show (SWord8 a) = "SWord8 (" ++ show a ++ ")" -- TODO: Not a proper implementation...
instance Show (Sing (a :: PWord16)) where
    show (SWord16 a) = "SWord16 (" ++ show a ++ ")" -- TODO: Not a proper implementation...
instance Show (Sing (a :: PWord32)) where
    show (SWord32 a) = "SWord32 (" ++ show a ++ ")" -- TODO: Not a proper implementation...
instance Show (Sing (a :: PWord64)) where
    show (SWord64 a) = "SWord64 (" ++ show a ++ ")" -- TODO: Not a proper implementation...

instance SingKind (PWord8) where
    type Demote (PWord8) = Word8
    fromSing (SWord8 (SFin :: Sing a)) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for PWord8. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SWord8 (SFin :: Sing a))

instance SingKind (PWord16) where
    type Demote (PWord16) = Word16
    fromSing (SWord16 (SFin :: Sing a)) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for PWord16. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SWord16 (SFin :: Sing a))

instance SingKind (PWord32) where
    type Demote (PWord32) = Word32
    fromSing (SWord32 (SFin :: Sing a)) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin SWord32. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SWord32 (SFin :: Sing a))

instance SingKind (PWord64) where
    type Demote (PWord64) = Word64
    fromSing (SWord64 (SFin :: Sing a)) = fromIntegral $ finVal @a
    toSing n = case someFinVal $ fromIntegral n of
        Nothing -> error $ show n ++ " out of bounds for Fin SWord64. This should not be possible."
        Just (SomeFin (_ :: Proxy a)) -> SomeSing (SWord64 (SFin :: Sing a))

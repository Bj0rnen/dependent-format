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
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module DepKDeserialize where

import Vector
import DepState
import Knowledge
import DepLevel

import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.Prelude.Maybe
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
import Data.Int
import Data.Bits
import Numeric.Natural
import Data.Kind.Fin (ltNat, predecessor, subNat)
import Data.Singletons.Fin

import Data.Reflection

import Control.Monad.State
import Control.Monad.Except


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
instance RequireAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS 'Known ds) where
    getAtom (KnowledgeCons (KnowledgeK s) _) = SomeSing s
instance
    -- TODO: Any hope of showing the name of the type variable?
    --  With nested records, it might've gone by multiple names, I suppose...
    --  Still, if type variable names are accessible, we could in theory show some kind of stack trace.
    TypeError (Text "A type variable of kind '" :<>: ShowType k :<>: Text "' is required before it is known.") =>
    RequireAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS 'Unknown ds) where
    getAtom = error "unreachable"
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


-- TODO: Add meaningful structure.
data DeserializeError = DeserializeError String
    deriving (Show)


data AnyK (f :: ks) where
    AnyK :: Proxy xs -> f :@@: InterpretVars xs -> AnyK f

class DepKDeserialize (f :: ks) where
    type Require (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint
    type Learn (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d
    depKSerialize :: AnyK f -> [Word8]
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  Require f as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK f, KnowledgeList (Learn f as ds))

    -- TODO: I was going for a DerivingVia design rather than default signatures, but that had problems.
    type Require (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) = RequireK (RepK f) as ds
    type Learn (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) = LearnK (RepK f) as ds
    default depKSerialize :: (forall xs. GenericK' f xs, DepKDeserializeK (RepK f)) => AnyK f -> [Word8]
    depKSerialize (AnyK (Proxy :: Proxy xs) a) =
        depKSerializeK (AnyKK @(RepK f) @xs (withDict (interpretVarsIsJustVars @xs) (fromK @_ @f @xs a \\ genericKInstance @f @xs)))
    default depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  (forall xs. GenericK' f xs, DepKDeserializeK (RepK f), RequireK (RepK f) as ds, Learn f as ds ~ LearnK (RepK f) as ds)
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK f, KnowledgeList (Learn f as ds))
    depKDeserialize p kl = do
        (AnyKK (r :: RepK f xs), kl') <- depKDeserializeK @_ @(RepK f) p kl
        -- TODO: This is messy. Could we at least make it so just one of interpretVarsIsJustVars genericKInstance is needed?
        return (AnyK (Proxy @xs) ((withDict (interpretVarsIsJustVars @xs) (toK @_ @f @xs r)) \\ genericKInstance @f @xs), kl')

-- TODO: Helper used while dropping the old Serialize class. Might not want to keep this.
class (DepKDeserialize a, Require a 'AtomNil 'DZ) => Serialize a
instance (DepKDeserialize a, Require a 'AtomNil 'DZ) => Serialize a
serialize :: forall a. Serialize a => a -> [Word8]
serialize a = depKSerialize (AnyK (Proxy @'LoT0) a)
deserialize :: forall a. Serialize a => ExceptT DeserializeError (State [Word8]) a
deserialize = do
    (AnyK _ a, _) <- depKDeserialize @Type @a (Proxy @'AtomNil) KnowledgeNil
    return a

instance DepKDeserialize Word8 where
    type Require Word8 as ds = ()
    type Learn Word8 as ds = ds
    depKSerialize (AnyK _ a) = [a]
    depKDeserialize Proxy kl = do
        (bs :: [Word8]) <- get
        case bs of
            [] -> throwError $ DeserializeError "No more bytes to read!"
            (b : bs') -> do
                put bs'
                return (AnyK (Proxy @'LoT0) b, kl)

instance DepKDeserialize Word16 where
    type Require Word16 as ds = ()
    type Learn Word16 as ds = ds
    depKSerialize (AnyK _ a) =
        [ fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    depKDeserialize _ kl = do
        bs <- deserialize @(Vector Word8 2)
        case bs of
            a :> b :> Nil ->
                return
                    (AnyK (Proxy @'LoT0)
                        (       (fromIntegral a) `shiftL` 8
                            .|. fromIntegral b
                        )
                    , kl
                    )

instance DepKDeserialize Word32 where
    type Require Word32 as ds = ()
    type Learn Word32 as ds = ds
    depKSerialize (AnyK _ a) =
        [ fromIntegral ((a `shiftR` 24) .&. 0xFF)
        , fromIntegral ((a `shiftR` 16) .&. 0xFF)
        , fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    depKDeserialize _ kl = do
        bs <- deserialize @(Vector Word8 4)
        case bs of
            a :> b :> c :> d :> Nil ->
                return
                    (AnyK (Proxy @'LoT0)
                        (       (fromIntegral a) `shiftL` 24
                            .|. (fromIntegral b) `shiftL` 16
                            .|. (fromIntegral c) `shiftL` 8
                            .|. fromIntegral d
                        )
                    , kl
                    )

instance DepKDeserialize Word64 where
    type Require Word64 as ds = ()
    type Learn Word64 as ds = ds
    depKSerialize (AnyK _ a) =
        [ fromIntegral ((a `shiftR` 56) .&. 0xFF)
        , fromIntegral ((a `shiftR` 48) .&. 0xFF)
        , fromIntegral ((a `shiftR` 40) .&. 0xFF)
        , fromIntegral ((a `shiftR` 32) .&. 0xFF)
        , fromIntegral ((a `shiftR` 24) .&. 0xFF)
        , fromIntegral ((a `shiftR` 16) .&. 0xFF)
        , fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    depKDeserialize _ kl = do
        bs <- deserialize @(Vector Word8 8)
        case bs of
            a :> b :> c :> d :> e :> f :> g :> h :> Nil ->
                return
                    (AnyK (Proxy @'LoT0)
                        (       (fromIntegral a) `shiftL` 56
                            .|. (fromIntegral b) `shiftL` 48
                            .|. (fromIntegral c) `shiftL` 40
                            .|. (fromIntegral d) `shiftL` 32
                            .|. (fromIntegral e) `shiftL` 24
                            .|. (fromIntegral f) `shiftL` 16
                            .|. (fromIntegral g) `shiftL` 8
                            .|. fromIntegral h
                        )
                        , kl
                    )

instance DepKDeserialize Int8 where
    type Require Int8 as ds = ()
    type Learn Int8 as ds = ds
    depKSerialize (AnyK _ a) = [fromIntegral a]
    depKDeserialize Proxy kl = do
        (bs :: [Word8]) <- get
        case bs of
            [] -> throwError $ DeserializeError "No more bytes to read!"
            (b : bs') -> do
                put bs'
                return (AnyK (Proxy @'LoT0) (fromIntegral b), kl)

-- TODO: This instance should go away.
instance DepKDeserialize Natural where  -- 8-bit
    type Require Natural as ds = ()
    type Learn Natural as ds = ds
    depKSerialize (AnyK _ a) = [fromIntegral a]
    depKDeserialize _ kl = do
        b <- deserialize @Word8
        return (AnyK (Proxy @'LoT0) (fromIntegral b), kl)

instance (SingKind k, Serialize (Demote k)) => DepKDeserialize (Sing :: k -> Type) where
    type Require (Sing :: k -> Type) as ds = LearnableAtom (AtomAt 'VZ as) ds
    type Learn (Sing :: k -> Type) as ds = LearnAtom (AtomAt 'VZ as) ds
    depKSerialize (AnyK _ a) = depKSerialize @_ @(Demote k) (AnyK Proxy (FromSing a))
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (k -> Type))
        .  Require (Sing :: k -> Type) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK (Sing :: k -> Type), KnowledgeList (Learn (Sing :: k -> Type) as ds))
    depKDeserialize _ kl = do
        d <- deserialize
        case d of
            FromSing (s :: Sing (s :: k)) ->
                case learnAtom @d @k @(AtomAt 'VZ as) (SomeSing s) kl of
                    Nothing -> throwError $ DeserializeError "Learned something contradictory"
                    Just kl' ->
                        return (AnyK (Proxy @(s :&&: 'LoT0)) s, kl')

instance (SingKind k, Serialize (Demote k), SDecide k, SingI a) => DepKDeserialize (Sing (a :: k)) where
    type Require (Sing (a :: k)) as ds = ()
    type Learn (Sing (a :: k)) _ ds = ds
    depKSerialize (AnyK _ a) = depKSerialize @_ @(Demote k) (AnyK Proxy (FromSing a))
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d Type)
        .  Require (Sing (a :: k)) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK (Sing (a :: k)), KnowledgeList (Learn (Sing (a :: k)) as ds))
    depKDeserialize _ kl = do
        d <- deserialize
        case d of
            FromSing (s :: Sing (s :: k)) ->
                case s %~ (sing @a) of
                    Disproved f ->
                        -- TODO: Can we show the expected and actual values?
                        --  A Show instance would be intrusive though. Maybe just show the bytes?
                        throwError $ DeserializeError "Deserialized a specified Sing and got another value than specified"
                    Proved Refl -> return (AnyK (Proxy @'LoT0) s, kl)

-- TODO: Is it sensible that this is indexed by a TyVar and not a Nat?
type family
    AtomAt (n :: TyVar ks k) (as :: AtomList d ks) :: Atom d k where
    AtomAt 'VZ (AtomCons a _) = a
    AtomAt ('VS v) (AtomCons _ as) = AtomAt v as

instance Serialize a => DepKDeserialize (Vector a) where
    type Require (Vector a) as ds = RequireAtom (AtomAt 'VZ as) ds
    type Learn (Vector a) _ ds = ds
    depKSerialize (AnyK (Proxy :: Proxy xs) a) =
        -- TODO: This approach seems more like a workaround than The Right Thing.
        --  There's computational cost to figuring out this length, and I don't know
        --  if this approach is possible in all cases (a Vector happens to be a
        --  "singleton" for its own length). Maybe the wrapper around the input
        --  (AnyK for now) is supposed to hold singletons for all the parts of `xs`
        --  which are the "target" of `Require`, i.e. 'VZ.
        withSingI (resolveLength a) $
            depKSerialize @_ @(Vector a (InterpretVar 'VZ xs)) (AnyK Proxy a)
        where
            resolveLength :: forall a n. Vector a n -> Sing n
            resolveLength Nil = SNat @0
            resolveLength (_ :> xs) =
                case resolveLength xs of
                    (SNat :: Sing m) -> SNat @(1 + m) \\ plusNat @1 @m
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Nat -> Type))
        .  Require (Vector a) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK (Vector a), KnowledgeList (Learn (Vector a) as ds))
    depKDeserialize _ kl =
        case getAtom @d @Nat @(AtomAt 'VZ as) @ds kl of
            SomeSing (SNat :: Sing n) -> do
                (a :: Vector a n) <- deserialize
                return (AnyK (Proxy @(n :&&: 'LoT0)) a, kl)

instance (Serialize a, SingI n) => DepKDeserialize (Vector a n) where
    type Require (Vector a n) as ds = ()
    type Learn (Vector a n) _ ds = ds
    depKSerialize (AnyK _ (v :: Vector a n)) =
        withKnownNat @n sing $
            Vector.ifZeroElse @n [] $ \_ ->
                case v of
                    x :> xs ->
                        depKSerialize (AnyK (Proxy @'LoT0) x) ++ depKSerialize (AnyK (Proxy @'LoT0) xs) \\ samePredecessor @n
    depKDeserialize _ kl =
        withKnownNat @n sing $
            Vector.ifZeroElse @n
                (return (AnyK (Proxy @'LoT0) Nil, kl))
                \(Proxy :: Proxy n1) -> do
                    a <- deserialize @a
                    as <- deserialize @(Vector a n1)
                    return (AnyK (Proxy @'LoT0) (a :> as), kl)


data AnyKK :: (LoT ks -> Type) -> Type where
    AnyKK :: f xs -> AnyKK f

class DepKDeserializeK (f :: LoT ks -> Type) where
    type RequireK (f :: LoT ks -> Type) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint
    type LearnK (f :: LoT ks -> Type) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d
    depKSerializeK :: AnyKK f -> [Word8]
    depKDeserializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  RequireK f as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyKK f, KnowledgeList (LearnK f as ds))

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

--given xs ~ (x0 :&&: x1 :&&: x2 :&&: x3 :&&: 'LoT0)
--and t ~ L0R1 :$: Var3 :@: Var3
--so AtomKonAtomList t ~ as ~ 'AtomCons Var3 ('AtomCons Var3 'AtomNil)
--we want L0R1 :@@: ys where ys ~ x3 :&&: x3 :&&: 'LoT0
--ys ~ Foo as xs

type family
    InterpretAll (as :: AtomList ks ks') (xs :: LoT ks) :: LoT ks' where
    InterpretAll 'AtomNil _ = 'LoT0
    InterpretAll ('AtomCons t as) xs = Interpret t xs :&&: InterpretAll as xs


instance (DepKDeserialize (AtomKonConstructor t)) => DepKDeserializeK (Field t) where
    type RequireK (Field t) as (ds :: DepStateList d) =
        Require (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds
    type LearnK (Field t) as (ds :: DepStateList d) =
        Learn (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds
    -- TODO: There's about a 1% chance that I got this right first try. That's a highly unproven unsafeCoerce, just guesswork.
    depKSerializeK (AnyKK (Field a :: Field t xs)) = depKSerialize @(AtomKonKind t) @(AtomKonConstructor t) (AnyK (Proxy @(InterpretAll (AtomKonAtomList t) xs)) (unsafeCoerce a))
    depKDeserializeK
        :: forall d (ds :: DepStateList d) as
        .  RequireK (Field t) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyKK (Field t), KnowledgeList (LearnK (Field t) as ds))
    depKDeserializeK _ kl = do
        (AnyK Proxy a, kl') <- depKDeserialize @(AtomKonKind t) @(AtomKonConstructor t) (Proxy @(DereferenceAtomList as (AtomKonAtomList t))) kl
        return (AnyKK (Field (unsafeCoerce a)), kl')

instance (DepKDeserializeK f, DepKDeserializeK g) => DepKDeserializeK (f :*: g) where
    type RequireK (f :*: g) as ds =
        ( RequireK f as ds
        , RequireK g as (LearnK f as ds)
        )
    type LearnK (f :*: g) as ds = LearnK g as (LearnK f as ds)
    depKSerializeK (AnyKK (a :*: b)) = depKSerializeK (AnyKK a) ++ depKSerializeK (AnyKK b)
    depKDeserializeK p kl = do
        (AnyKK a, kl') <- depKDeserializeK @_ @f p kl
        (AnyKK b, kl'') <- depKDeserializeK @_ @g p kl'
        return (AnyKK (unsafeCoerce a :*: b), kl'')  -- TODO: Would be excellent to get rid of unsafeCoerce!

instance DepKDeserializeK f => DepKDeserializeK (M1 i c f) where
    type RequireK (M1 i c f) as ds = RequireK f as ds
    type LearnK (M1 i c f) as ds = LearnK f as ds
    depKSerializeK (AnyKK (M1 a)) = depKSerializeK (AnyKK a)
    depKDeserializeK p kl = do
        (AnyKK a, kl') <- depKDeserializeK @_ @f p kl
        return (AnyKK (M1 a), kl')

instance DepKDeserializeK U1 where
    type RequireK U1 as ds = ()
    type LearnK U1 as ds = ds
    depKSerializeK _ = []
    depKDeserializeK p kl = return (AnyKK U1, kl)


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
    depKSerializeK (AnyKK (Exists a)) = depKSerializeK (AnyKK a)
    depKDeserializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  RequireK (Exists k (f :: LoT (k -> ks) -> Type)) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyKK (Exists k (f :: LoT (k -> ks) -> Type)), KnowledgeList (LearnK (Exists k (f :: LoT (k -> ks) -> Type)) as ds))
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


data Let (f :: a ~> b) (x :: a) (y :: b) where
    Let :: f @@ x :~: y -> Let f x y
    deriving (Show)


instance SingI f => DepKDeserialize (Let f :: a -> b -> Type) where
    type Require (Let f :: a -> b -> Type) as ds = (RequireAtom (AtomAt 'VZ as) ds, LearnableAtom (AtomAt ('VS 'VZ) as) ds)
    type Learn (Let f :: a -> b -> Type) as ds = LearnAtom (AtomAt ('VS 'VZ) as) ds
    depKSerialize (AnyK (Proxy :: Proxy xs) (Let Refl)) = []
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (a -> b -> Type))
        .  Require (Let f :: a -> b -> Type) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK (Let f :: a -> b -> Type), KnowledgeList (Learn (Let f :: a -> b -> Type) as ds))
    depKDeserialize _ kl =
        case getAtom @d @a @(AtomAt 'VZ as) @ds kl of
            SomeSing (x :: Sing x) ->
                case learnAtom @d @b @(AtomAt ('VS 'VZ) as) (SomeSing (sing @f @@ x)) kl of
                    Nothing -> throwError $ DeserializeError "Learned something contradictory while Let-binding"
                    Just kl' ->
                        return (AnyK (Proxy @(x :&&: Apply f x :&&: 'LoT0)) (Let Refl), kl')


data LetFromJust (f :: a ~> Maybe b) (x :: a) (y :: b) where
    LetFromJust :: f @@ x :~: 'Just y -> LetFromJust f x y
    deriving (Show)

instance SingI f => DepKDeserialize (LetFromJust f :: a -> b -> Type) where
    type Require (LetFromJust f :: a -> b -> Type) as ds = (RequireAtom (AtomAt 'VZ as) ds, LearnableAtom (AtomAt ('VS 'VZ) as) ds)
    type Learn (LetFromJust f :: a -> b -> Type) as ds = LearnAtom (AtomAt ('VS 'VZ) as) ds
    depKSerialize (AnyK (Proxy :: Proxy xs) (LetFromJust Refl)) = []
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (a -> b -> Type))
        .  Require (LetFromJust f :: a -> b -> Type) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK (LetFromJust f :: a -> b -> Type), KnowledgeList (Learn (LetFromJust f :: a -> b -> Type) as ds))
    depKDeserialize _ kl =
        case getAtom @d @a @(AtomAt 'VZ as) @ds kl of
            SomeSing (x :: Sing x) ->
                case sing @f @@ x of
                    SNothing -> throwError $ DeserializeError "LetFromJust-binding failed because it resulted in Nothing"
                    (SJust (s :: Sing y)) ->
                        case learnAtom @d @b @(AtomAt ('VS 'VZ) as) (SomeSing s) kl of
                            Nothing -> throwError $ DeserializeError "Learned something contradictory while LetFromJust-binding"
                            Just kl' ->
                                return (AnyK (Proxy @(x :&&: y :&&: 'LoT0)) (LetFromJust Refl), kl')

{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE UndecidableInstances #-}

module BitMap where

import DepKDeserialize
import DepKDeserializeWord
import DepKDeserializeLet
import Generics.Kind hiding (Nat)
import Generics.Kind.TH

import ASCII
import Data.Word
import Vector
import Data.Singletons.Fin
import Data.Type.Equality
import Control.Monad.State

{-
data BitMap = forall (width :: Promoted Word8) (height :: Promoted Word8). BitMap
    { bmp    :: ASCII "BMP"
    , width  :: Sing width
    , height :: Sing height
    , pixels :: GVector (GVector Word8 width) height
    }
deriving instance Show BitMap
$(deriveGenericK ''BitMap)
deriving instance DepKDeserialize BitMap

testSerializeEmpty = serialize (BitMap { width = SPromoted (SFin @256 @('Fin 0)), height = SPromoted (SFin @256 @('Fin 0)), pixels = GVector (Let Refl) Nil })
-}

import GHC.TypeNats
import Data.Singletons
import Data.Singletons.TypeLits
import Data.Constraint
import DepState
import Data.Kind
import Control.Monad.Indexed

data BitMap = forall (width :: Nat) (height :: Nat). BitMap
    { bmp    :: ASCII "BMP"
    , width  :: Sing width
    , height :: Sing height
    , pixels :: Vector Word8 height
    }
deriving instance Show BitMap

-- $(deriveGenericK ''BitMap)
instance GenericK BitMap 'LoT0 where
    type RepK BitMap =
        Exists Nat (
            Exists Nat (
                    Field ('Kon (ASCII "BMP"))
                :*: Field ('Kon Sing :@: 'Var 'VZ)
                :*: Field ('Kon Sing :@: 'Var ('VS 'VZ))
                :*: Field ('Kon Vector :@: 'Kon Word8 :@: 'Var ('VS 'VZ))
            )
        )
    fromK (BitMap {..}) =
        Exists (Exists (Field bmp :*: Field width :*: Field height :*: Field pixels))
    toK (Exists (Exists (Field bmp :*: Field width :*: Field height :*: Field pixels))) =
        BitMap {..}
deriving instance DepKDeserialize BitMap

testSerializeEmpty = serialize (BitMap { bmp = ASCII, width = (SNat @0), height = (SNat @0), pixels = Nil })
testDeserializeEmpty = runStateT (deserialize @BitMap) [66,77,80,0,0]

--testDict :: Dict (
--    RequireK
--        (Field ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
--        ('AtomCons ('Var ('VZ)) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
--        ('DS 'Known ('DS 'Known 'DZ))
--    )


--Require
--    Vector
--    ('AtomCons
--        (DereferenceAtom
--            ('AtomCons
--                Var0
--                ('AtomCons
--                    ('Var ('VS 'VZ))
--                    'AtomNil
--                )
--            )
--            ('Kon (Vector Word8) ':@: 'Var 'VZ)
--        )
--        ('AtomCons ('Var ('VS 'VZ)) 'AtomNil)
--    )
--    ('DS 'Known ('DS 'Known 'DZ))


{-
    type RequireK (Field t) as (ds :: DepStateList d) =
        Require (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds
-}
--testDict :: Dict (
--    Require
--        (AtomKonConstructor ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
--        (DereferenceAtomList ('AtomCons ('Var ('VZ)) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil)) (AtomKonAtomList ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ))))
--        ('DS 'Known ('DS 'Known 'DZ))
--    )

-- (AtomKonConstructor ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
-- ~
-- Vector
--
-- (AtomKonAtomList ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
-- ~
-- 'AtomCons ('Kon (Vector Word8) ':@: 'Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil)
--
-- (DereferenceAtomList ('AtomCons ('Var ('VZ)) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil)) (AtomKonAtomList ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ))))
-- ~
-- 'AtomCons ('Kon (Vector Word8) ':@: 'Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil)

--testDict :: Dict (
--    Require
--        Vector
--        ('AtomCons ('Kon (Vector Word8) ':@: 'Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
--        ('DS 'Known ('DS 'Known 'DZ))
--    )

type family
    AllSame (xs :: [k]) :: Constraint where
    AllSame '[] = ()
    AllSame (x ': '[]) = ()
    AllSame (x ': y ': xs) = (x ~ y, AllSame (y ': xs))

testDict1 ::
    Dict (
        AllSame
        '[
            RequireK
                (Field ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
                ('AtomCons ('Var ('VZ)) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
                ('DS 'Known ('DS 'Known 'DZ))
        ,
            Require
                (AtomKonConstructor ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
                (DereferenceAtomList
                    ('AtomCons ('Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
                    (AtomKonAtomList ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
                )
                ('DS 'Known ('DS 'Known 'DZ))
        ,
            Require
                Vector
                --('AtomCons ('Kon (Vector Word8) :@: 'Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
                ('AtomCons
                    (DereferenceAtom
                        ('AtomCons ('Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
                        ('Kon (Vector Word8) ':@: 'Var 'VZ)
                    )
                    ('AtomCons ('Var ('VS 'VZ)) 'AtomNil)
                )
                ('DS 'Known ('DS 'Known 'DZ))
        ])
testDict1 = Dict

testDict2 ::
    Dict (
        AllSame
        '[  RequireK
                (Field ('Kon Vector :@: 'Kon Word8 :@: 'Var 'VZ))
                ('AtomCons ('Var 'VZ) 'AtomNil)
                ('DS 'Known 'DZ)
        ,   Require
                (AtomKonConstructor ('Kon Vector :@: 'Kon Word8 :@: 'Var 'VZ))
                (DereferenceAtomList
                    ('AtomCons ('Var 'VZ) 'AtomNil)
                    (AtomKonAtomList ('Kon Vector :@: 'Kon Word8 :@: 'Var 'VZ))
                )
                ('DS 'Known 'DZ)
        ,   Require
                Vector
                (DereferenceAtomList
                    ('AtomCons ('Var 'VZ) 'AtomNil)
                    ('AtomCons ('Kon Word8) ('AtomCons ('Var 'VZ) 'AtomNil))
                )
                ('DS 'Known 'DZ)
        ,   Require
                Vector
                ('AtomCons ('Kon Word8) ('AtomCons ('Var 'VZ) 'AtomNil))
                ('DS 'Known 'DZ)
        ])
testDict2 = Dict


--instance DepKDeserialize (Vector :: Type -> Nat -> Type) where
--    type Require
--        (Vector :: Type -> Nat -> Type)
--        ('AtomCons ('Kon f ':@: a) as :: AtomList d (Type -> Nat -> Type))  -- TODO: f must be a unary constructor?
--        (ds :: DepStateList d) =
--            ( ()
--            --, DepKDeserialize f
--            --, Require f ('AtomCons a 'AtomNil) ds
--            --, RequireAtom (AtomAt 'VZ as) ds
--            )
--    type Learn (Vector :: Type -> Nat -> Type) as ds = ds
--    depKSerialize (AnyK (Proxy :: Proxy (xs :: LoT (Type -> Nat -> Type))) v) = undefined
--        --case v of
--        --    Nil -> []
--        --    x :> xs ->
--        --        depKSerialize (AnyK (Proxy @'LoT0) x) ++ depKSerialize (AnyK (Proxy @'LoT0) xs) \\ samePredecessor @(InterpretVar ('VS 'VZ) xs)
--    --depKDeserialize
--    --    :: forall k d (ds :: DepStateList d) (f :: k -> Type) (a :: Atom d k) (as :: AtomList d (Nat -> Type))
--    --    .  Require (Vector :: Type -> Nat -> Type) ('AtomCons ('Kon f ':@: a) as :: AtomList d (Type -> Nat -> Type)) ds
--    --    => Proxy as -> IxGet ds (Learn (Vector :: Type -> Nat -> Type) ('AtomCons ('Kon f ':@: a) as :: AtomList d (Type -> Nat -> Type)) ds) (AnyK (Vector :: Type -> Nat -> Type))
--    depKDeserialize _ = undefined
--    --    igetAtom @d @k @(AtomAt 'VZ as) @ds >>>= \(SomeSing (lol :: Sing x)) ->
--    --    igetAtom @d @Nat @(AtomAt ('VS 'VZ) as) @ds >>>= \(SomeSing (SNat :: Sing n)) ->
--    --    fmap (AnyK (Proxy @(n :&&: 'LoT0))) $ withoutKnowledge $
--    --        withKnownNat @n sing $
--    --            Vector.ifZeroElse @n
--    --                (return Nil)
--    --                \(Proxy :: Proxy n1) -> do
--    --                    a <- deserialize @(f x)
--    --                    as <- deserialize @(Vector (f x) n1)
--    --                    return (a :> as)



instance DepKDeserialize (Vector :: Type -> Nat -> Type) where
    type Require
        (Vector :: Type -> Nat -> Type)
        (as :: AtomList d (Type -> Nat -> Type))
        (ds :: DepStateList d) =
            ( ()
            --, d ~ (Nat -> Type)
            --, ds ~ 'DS 'Known 'DZ
            --, as ~ ('AtomCons (AtomAt 'VZ as) ('AtomCons (AtomAt ('VS 'VZ) as) 'AtomNil))
            , AtomKonKind (AtomAt 'VZ as) ~ Type
            , AtomAt 'VZ as ~ 'Kon Word8  -- TODO: Obviously a silly constraint, but just pinning it down for the moment.
            --, AtomKonConstructor ('Kon Word8) ~ Word8
            --, Require (AtomKonConstructor (AtomAt 'VZ as)) 'AtomNil 'DZ

            --, Require (AtomKonConstructor (AtomAt 'VZ as)) (DereferenceAtomList as (AtomKonAtomList (AtomAt 'VZ as))) 'DZ
            , DepKDeserialize (AtomKonConstructor (AtomAt 'VZ as))
            , Require (AtomKonConstructor (AtomAt 'VZ as)) (AtomKonAtomList (AtomAt 'VZ as)) ds
            , RequireAtom (AtomAt ('VS 'VZ) as) ds
            )
    type Learn (Vector :: Type -> Nat -> Type) as ds = ds
    depKSerialize (AnyK (Proxy :: Proxy (xs :: LoT (Type -> Nat -> Type))) v) = undefined
        --case v of
        --    Nil -> []
        --    x :> xs ->
        --        depKSerialize (AnyK (Proxy @'LoT0) x) ++ depKSerialize (AnyK (Proxy @'LoT0) xs) \\ samePredecessor @(InterpretVar ('VS 'VZ) xs)
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Type -> Nat -> Type))
        .  Require (Vector :: Type -> Nat -> Type) (as :: AtomList d (Type -> Nat -> Type)) ds
        => Proxy as -> IxGet ds (Learn (Vector :: Type -> Nat -> Type) (as :: AtomList d (Type -> Nat -> Type)) ds) (AnyK (Vector :: Type -> Nat -> Type))
    depKDeserialize _ =
        igetAtom @d @Nat @(AtomAt ('VS 'VZ) as) @ds >>>= \(SomeSing (SNat :: Sing n)) ->
        fmap (AnyK (Proxy @((AtomKonConstructor (AtomAt 'VZ as)) :&&: n :&&: 'LoT0))) $ withoutKnowledge $
            withKnownNat @n sing $
                Vector.ifZeroElse @n
                    (return Nil)
                    \(Proxy :: Proxy n1) -> do
                        a <- deserialize @(AtomKonConstructor (AtomAt 'VZ as))
                        as <- deserialize @(Vector (AtomKonConstructor (AtomAt 'VZ as)) n1)
                        return (a :> as)

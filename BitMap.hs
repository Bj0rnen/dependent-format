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
{-# LANGUAGE FlexibleInstances #-}

module BitMap where

import DepKDeserialize
import DepKDeserializeWord
import DepKDeserializeLet
import Generics.Kind hiding (Nat, (:~:))
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
import Unsafe.Coerce
import GHC.TypeLits
import Control.Monad.Indexed.State
import Knowledge

data BitMap (width :: Nat) (height :: Nat) = BitMap
    { bmp    :: ASCII "BMP"
    , width  :: Sing width
    , height :: Sing height
    , pixels :: Vector (Vector Word8 width) height
    } deriving (Show)
--deriving instance Show (BitMap width height)

$(deriveGenericK ''BitMap)
--instance GenericK BitMap 'LoT0 where
--    type RepK BitMap =
--        Exists Nat (
--            Exists Nat (
--                    Field ('Kon (ASCII "BMP"))
--                :*: Field ('Kon Sing :@: 'Var 'VZ)
--                :*: Field ('Kon Sing :@: 'Var ('VS 'VZ))
--                :*: Field ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ))
--            )
--        )
--    fromK (BitMap {..}) =
--        Exists (Exists (Field bmp :*: Field width :*: Field height :*: Field pixels))
--    toK (Exists (Exists (Field bmp :*: Field width :*: Field height :*: Field pixels))) =
--        BitMap {..}
--deriving instance DepKDeserialize BitMap
deriving instance SingI width => DepKDeserialize (BitMap width)
deriving instance (SingI width, SingI height) => DepKDeserialize (BitMap width height)

testSerializeEmpty = serialize (BitMap { bmp = ASCII, width = (SNat @0), height = (SNat @0), pixels = Nil })
--testDeserializeEmpty = --runStateT (deserialize @BitMap) [66,77,80,0,0]
--    case runIxStateT
--            (runIxGet $ depKDeserialize @_ @BitMap (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))))
--            ((KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU KnowledgeNil)), [66,77,80,0,0]) of
--        Left e -> show e
--        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a
testSerializeNonEmpty = serialize (BitMap { bmp = ASCII, width = (SNat @2), height = (SNat @2), pixels = (0 :> 1 :> Nil) :> (2 :> 3 :> Nil) :> Nil })
--testDeserializeNonEmpty = --runStateT (deserialize @BitMap) [66,77,80,2,2,0,1,2,3]
--    case runIxStateT
--            (runIxGet $ depKDeserialize @_ @BitMap (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))))
--            ((KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU KnowledgeNil)), [66,77,80,2,2,0,1,2,3]) of
--        Left e -> show e
--        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a

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
        '[  RequireK
                (Field ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
                ('AtomCons ('Var ('VZ)) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
                ('DS 'Known ('DS 'Known 'DZ))
        ,   Require
                (AtomKonConstructor ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
                (DereferenceAtomList
                    ('AtomCons ('Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
                    (AtomKonAtomList ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ)))
                )
                ('DS 'Known ('DS 'Known 'DZ))
        ,   Require
                Vector
                ('AtomCons
                    (DereferenceAtom
                        ('AtomCons ('Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil))
                        ('Kon (Vector Word8) :@: 'Var 'VZ)
                    )
                    ('AtomCons ('Var ('VS 'VZ)) 'AtomNil)
                )
                ('DS 'Known ('DS 'Known 'DZ))
        ,   Require
                Vector
                ('AtomCons
                    ('Kon (Vector Word8) :@: 'Var 'VZ)
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

testDict3 ::
    Dict (
        AllSame
        '[  SerConstraintsK
                (Exists Nat
                    (Exists Nat
                        (   Field ('Kon (ASCII "BMP")) :*: Field ('Kon Sing :@: 'Var 'VZ) :*: Field ('Kon Sing :@: 'Var ('VS 'VZ)) :*: Field ('Kon Vector :@: ('Kon (Vector Word8) :@: 'Var 'VZ) :@: 'Var ('VS 'VZ))
                        )
                    )
                )
                'LoT0
        ])
testDict3 = Dict


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


-- TODO: This is surely not the right type for this.
--  I just have some vague idea that there should be a method
--  corresponding to Require, carrying the term-level information
--  that corresponds to the constraint, as if Require was a
--  typeclass. And maybe it should be that.
--  the point is, when a DepKDeserialize instance has a Require
--  instance that says `RequireAtom foo ds`, then you can go and
--  write `igetAtom @_ @_ @foo @ds` to get that "value" back as
--  a singleton.
--  But if your DepKDeserialize instance has a Require instance
--  that says `Require f as ds`, then how do you consume the
--  required knowledge at the term level?
--  For reference,  DepKDeserializeK (Field t) actually has
--  something like that, but it seems to get away with only a
--  call to depKDeserialize. Then it unsafeCoerces anyway,
--  because AnyK is useless, I guess. Anyway, now, we don't want
--  to deserialize anything, but rather expect.............
--
--  After that bit of rambling, maybe I don't need anything here?
--  Maybe just using depKDeserialize is what I needed after all?
--require :: Require f as ds => Proxy as -> Proxy ds -> Proxy f
--require = undefined

{-
instance DepKDeserialize (Vector :: Type -> Nat -> Type) where
    type SerConstraints (Vector :: Type -> Nat -> Type) xs = Serialize (HeadLoT xs)
    type Require
        (Vector :: Type -> Nat -> Type)
        (as :: AtomList d (Type -> Nat -> Type))
        (ds :: DepStateList d) =
            ( ()
            , d ~ (Nat -> Nat -> Type)
            --, ds ~ ('DS 'Known ('DS 'Known 'DZ))
            --, as ~ ('AtomCons (AtomAt 'VZ as) ('AtomCons (AtomAt ('VS 'VZ) as) 'AtomNil))
            --, Require (AtomKonConstructor (AtomAt 'VZ as)) 'AtomNil 'DZ
            --, Require (AtomKonConstructor (AtomAt 'VZ as)) (DereferenceAtomList as (AtomKonAtomList (AtomAt 'VZ as))) 'DZ

            , AtomKonKind (AtomAt 'VZ as) ~ (Nat -> Type)
            --, AtomAt 'VZ as ~ ('Kon (Vector Word8) :@: 'Var 'VZ)  -- TODO: Obviously a silly constraint, but just pinning it down for the moment.
            --, AtomKonConstructor (AtomAt 'VZ as) ~ Vector Word8
            , DepKDeserialize (AtomKonConstructor (AtomAt 'VZ as))
            , Require (AtomKonConstructor (AtomAt 'VZ as)) (AtomKonAtomList (AtomAt 'VZ as)) ds
            , RequireAtom (AtomAt ('VS 'VZ) as) ds
            )
    type Learn (Vector :: Type -> Nat -> Type) as ds = ds
    depKSerialize (TheseK (Proxy :: Proxy (xs :: LoT (Type -> Nat -> Type))) v) =
        case unsafeCoerce (Refl @xs) :: xs :~: (a :&&: n :&&: 'LoT0) of
            Refl ->
                case v of
                    Nil -> []
                    x :> xs ->
                        depKSerialize (TheseK (Proxy @'LoT0) x) ++ depKSerialize (TheseK (Proxy @'LoT0) xs) \\ samePredecessor @(InterpretVar ('VS 'VZ) xs)
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Type -> Nat -> Type))
        .  Require (Vector :: Type -> Nat -> Type) (as :: AtomList d (Type -> Nat -> Type)) ds
        => Proxy as -> IxGet ds (Learn (Vector :: Type -> Nat -> Type) (as :: AtomList d (Type -> Nat -> Type)) ds) (AnyK (Vector :: Type -> Nat -> Type))
    depKDeserialize (Proxy :: Proxy as) =
        case unsafeCoerce (Refl @as) ::
            as :~: 'AtomCons ('Kon (Vector Word8) :@: 'Var 'VZ) ('AtomCons ('Var ('VS 'VZ)) 'AtomNil) of
            Refl ->
                --case Dict @
                --    ( ()
                --    , AtomAt 'VZ as ~ ('Kon (Vector Word8) :@: 'Var 'VZ)
                --    , AtomKonConstructor (AtomAt 'VZ as) ~ Vector Word8
                --    , AtomKonAtomList ('Kon (Vector Word8) :@: 'Var 'VZ) ~ 'AtomCons ('Var 'VZ) 'AtomNil) of  -- Just checking. This follows form the above axiom.
                --    Dict ->
                        igetAtom @d @Nat @(AtomAt ('VS 'VZ) as) @ds >>>= \(SomeSing (SNat :: Sing n)) ->
                        withKnownNat @n sing $
                            Vector.ifZeroElse @n
                                (return (AnyK (Proxy @(_ :&&: 0 :&&: 'LoT0)) Nil))
                                \(Proxy :: Proxy n1) ->
                                    depKDeserialize
                                        @(AtomKonKind (AtomAt 'VZ as))
                                        @(AtomKonConstructor (AtomAt 'VZ as))
                                        (Proxy @(AtomKonAtomList (AtomAt 'VZ as))) >>>= \(AnyK Proxy a) ->
                                    depKDeserialize
                                        @(Type -> Nat -> Type)
                                        @Vector
                                        (Proxy @('AtomCons (AtomAt 'VZ as) ('AtomCons ('Kon n1) 'AtomNil))) >>>= \(AnyK Proxy as) ->
                                    return (AnyK Proxy (unsafeCoerce (a :> unsafeCoerce as)))
-}

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
{-# LANGUAGE DuplicateRecordFields #-}

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
$(deriveGenericK ''BitMap)
deriving instance DepKDeserialize BitMap
deriving instance DepKDeserialize (BitMap width)
deriving instance DepKDeserialize (BitMap width height)

data BitMapExt = forall (width :: Nat) (height :: Nat). BitMapExt
    { bmp    :: ASCII "BMP"
    , width  :: Sing width
    , height :: Sing height
    , pixels :: Vector (Vector Word8 width) height
    }
deriving instance Show BitMapExt
$(deriveGenericK ''BitMapExt)
deriving instance DepKDeserialize BitMapExt

testSerializeEmpty = --serialize (BitMap { bmp = ASCII, width = (SNat @0), height = (SNat @0), pixels = Nil })
    depKSerialize (TheseK (Proxy @(_ :&&: _ :&&: 'LoT0)) (BitMap { bmp = ASCII, width = (SNat @0), height = (SNat @0), pixels = Nil }))
testDeserializeEmpty = --runStateT (deserialize @BitMapExt) [66,77,80,0,0]
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @BitMap (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))))
            ((KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU KnowledgeNil)), [66,77,80,0,0]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a
testSerializeNonEmpty = --serialize (BitMap { bmp = ASCII, width = (SNat @2), height = (SNat @2), pixels = (0 :> 1 :> Nil) :> (2 :> 3 :> Nil) :> Nil })
    depKSerialize (TheseK (Proxy @(_ :&&: _ :&&: 'LoT0)) (BitMap { bmp = ASCII, width = (SNat @2), height = (SNat @2), pixels = (0 :> 1 :> Nil) :> (2 :> 3 :> Nil) :> Nil }))
testDeserializeNonEmpty = --runStateT (deserialize @BitMapExt) [66,77,80,2,2,0,1,2,3]
    case runIxStateT
            (runIxGet $ depKDeserialize @_ @BitMap (Proxy @(AtomCons Var0 (AtomCons Var1 AtomNil))))
            ((KnowledgeCons KnowledgeU (KnowledgeCons KnowledgeU KnowledgeNil)), [66,77,80,2,2,0,1,2,3]) of
        Left e -> show e
        Right (AnyK (Proxy :: Proxy xs) a, _) -> show a


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

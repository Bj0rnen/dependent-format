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

module Generic1K where

import Serialize
import Vector
import SingLoT
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

import Exinst
import Data.Reflection


-- TODO: Needs further cleanup

instance Serialize (f p) => Serialize (GHC.Rec1 f p) where
    serialize (GHC.Rec1 a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (GHC.Rec1 a, bs')

instance Serialize (f p) => Serialize (GHC.M1 i c f p) where
    serialize (GHC.M1 a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (GHC.M1 a, bs')

instance (Serialize (a p), Serialize (b p)) => Serialize ((a GHC.:*: b) p) where
    serialize (a GHC.:*: b) = serialize a ++ serialize b
    deserialize bs =
        case deserialize @(a p) bs of
            (a, bs') ->
                case deserialize @(b p) bs' of
                    (b, bs'') -> (a GHC.:*: b, bs'')

instance Serialize a => Serialize (GHC.K1 i a p) where
    serialize (GHC.K1 a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (GHC.K1 a, bs')

instance Serialize (GHC.U1 p) where
    serialize GHC.U1 = []
    deserialize bs = (GHC.U1, bs)

instance Serialize (Some1 f) => Serialize (Some1 (GHC.M1 i c f)) where
    serialize (Some1 (s :: Sing a) (GHC.M1 a)) = serialize (Some1 s a)
    deserialize bs =
        case deserialize bs of
            (Some1 s a, bs') -> (Some1 s (GHC.M1 a), bs')
instance Serialize (Some1 f) => Serialize (Some1 (GHC.Rec1 f)) where
    serialize (Some1 s (GHC.Rec1 a)) = serialize (Some1 s a)
    deserialize bs =
        case deserialize bs of
            (Some1 s a, bs') -> (Some1 s (GHC.Rec1 a), bs')
--instance Serialize (Some1 (GHC.K1 i a)) where
--    serialize (Some1 s (GHC.K1 a)) = serialize a
--    deserialize bs =
--        case deserialize bs of
--            (a, bs') -> (Some1 ? (GHC.K1 a), bs')

serializeSome1 :: (GHC.Generic1 f, Serialize (Some1 (GHC.Rep1 f))) => Some1 f -> [Word8]
serializeSome1 (Some1 s a) = serialize (Some1 s (GHC.from1 a))
deserializeSome1 :: (GHC.Generic1 f, Serialize (Some1 (GHC.Rep1 f))) => [Word8] -> (Some1 f, [Word8])
deserializeSome1 bs =
    case deserialize bs of
        (Some1 (s :: Sing a) a, bs') ->
            (Some1 s (GHC.to1 a), bs')


newtype Generic1Wrapper f a = Generic1Wrapper { unwrapGeneric1 :: f a }
instance (GHC.Generic1 f, Serialize (GHC.Rep1 f x), HasDepLevel f) => Serialize (Generic1Wrapper f x) where
    serialize (Generic1Wrapper a) = serialize $ GHC.from1 a
    deserialize bs =
        case deserialize bs of
            (a, bs') ->
                (Generic1Wrapper (GHC.to1 a), bs')

newtype GenericKWrapper f a = GenericKWrapper { unwrapGenericK :: f :@@: a }
instance (GenericK f x, Serialize (RepK f x), HasDepLevel f) => Serialize (GenericKWrapper f x) where
    serialize (GenericKWrapper a) = serialize $ fromK @_ @f @x a
    deserialize bs =
        case deserialize bs of
            (a, bs') ->
                (GenericKWrapper (toK @_ @f @x a), bs')
--newtype Generic1KWrapper f a = Generic1KWrapper { unwrapGeneric1K :: f :@@: (a :&&: LoT0) }
--instance (GenericK f (a :&&: LoT0), Serialize (RepK f (a :&&: LoT0)), HasDepLevel f) => Serialize (Generic1KWrapper f a) where
--    serialize (Generic1KWrapper a) = serialize $ fromK @_ @f @(a :&&: LoT0) a
--    deserialize bs =
--        case deserialize bs of
--            (a, bs') ->
--                (Generic1KWrapper (toK @_ @f @(a :&&: LoT0) a), bs')

instance Serialize (f (Interpret (Var VZ) xs)) => Serialize (Field (f :$: Var0) xs) where
    serialize (Field a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (Field a, bs')
instance Serialize a => Serialize (Field ('Kon a) vs) where
    serialize (Field a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (Field a, bs')

--newtype Rep1K :: (k -> Type) -> k -> Type where
--    Rep1K :: RepK f (a :&&: LoT0) -> Rep1K f a
--serializeSome1K :: forall f. (forall x. GenericK f (x :&&: LoT0), Serialize (Some1 (Rep1K f))) => Some1 f -> [Word8]
--serializeSome1K (Some1 s a) = serialize (Some1 s (Rep1K @f (fromK a)))
--deserializeSome1K :: forall f. (forall x. GenericK f (x :&&: LoT0), Serialize (Some1 (Rep1K f))) => [Word8] -> (Some1 f, [Word8])
--deserializeSome1K bs =
--    case deserialize bs of
--        (Some1 (s :: Sing a) (Rep1K a :: Rep1K f a), bs') ->
--            (Some1 s (toK a), bs')

instance HasDepLevel (Field (Kon f :@: Var VZ)) where
    type DepLevelOf (Field (Kon f :@: Var VZ)) = DepLevelOf f
--    Equivalently
--instance HasDepLevel (Field (f :$: Var0)) where
--    type DepLevelOf (Field (f :$: Var0)) = DepLevelOf f
--------------------------instance Product1Serialize
--------------------------    (DepLevelOf (GHC.Rep1 UnitWithSize))
--------------------------    (ProductDepLevel 'Learning (DepLevelOf (GHC.Rep1 RequiringSize)))
--------------------------    (Field (UnitWithSize :$: Var0))
--------------------------    (Field (Sing :$: Var0) :*: Field (RequiringSize :$: Var0))

-- TODO: Can it be written in terms of (Dict1 c (f :: Nat -> Type))?
instance (forall x. KnownNat x => c (f (x ':&&: 'LoT0))) => Dict1 c (f :: LoT (Nat -> Type) -> Type) where
    dict1 (SNat :&&&: SLoT0) = Dict

--instance Serialize (Some1 f) => Serialize (Some1 (Field (f :$: Var0))) where
--    serialize (Some1 (SLoT1 s) (Field a)) = serialize (Some1 s a)
--    deserialize bs =
--        case deserialize @(Some1 f) bs of
--            (Some1 (s :: Sing a) a :: Some1 f, bs') ->
--                (Some1 (SLoT1 s :: Sing (a :&&: LoT0)) (Field a :: Field (f :$: Var0) (a :&&: LoT0)) :: Some1 (Field (f :$: Var0)), bs')
--                --(Some1 (SLoT1 s :: Sing (k :&&: LoT0)) (Field a), bs')

instance Serialize (Some1 f) => Serialize (Some1 (Field ('Kon f ':@: 'Var 'VZ :: Atom (k -> Type) Type))) where
    serialize (Some1 (s :&&&: SLoT0) (Field a)) = serialize (Some1 s a)
    deserialize bs =
        case deserialize bs of
            (Some1 s a, bs') ->
                (Some1 (s :&&&: SLoT0) (Field a), bs')

--instance Serialize (Some1 (RepK f :: LoT (k -> Type) -> Type)) => Serialize (Some1 (Rep1K f :: k -> Type)) where
--    serialize (Some1 s (Rep1K (a :: RepK f (a :&&: LoT0)) :: Rep1K f a)) = serialize (Some1 undefined a)
--    deserialize bs = undefined

serializeSome1K :: forall f. (forall x. GenericK f (x :&&: LoT0), Serialize (Some1 (RepK f))) => Some1 f -> [Word8]
serializeSome1K (Some1 s a) = serialize (Some1 (s :&&&: SLoT0) (fromK a))
deserializeSome1K :: forall f. (forall x. GenericK f (x :&&: LoT0), Serialize (Some1 (RepK f))) => [Word8] -> (Some1 f, [Word8])
deserializeSome1K bs =
    case deserialize @(Some1 (RepK f)) bs of
        (Some1 (s :&&&: SLoT0) a, bs') ->
            (Some1 s (toK a), bs')

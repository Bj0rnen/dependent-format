{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module DepKDeserializeLet where

import DepKDeserialize

import Data.Singletons
import Data.Singletons.Prelude.Maybe
import Data.Type.Equality
import Data.Kind
import Generics.Kind hiding ((:~:))
import Generics.Kind.TH

import Data.Word

import Control.Monad.Except
import Control.Monad.State


data Let (f :: a ~> b) (x :: a) (y :: b) where
    Let :: f @@ x :~: y -> Let f x y
    deriving (Show)


instance DepKDeserialize (Let :: (a ~> b) -> a -> b -> Type) where
    type Require (Let :: (a ~> b) -> a -> b -> Type) as ds = (RequireAtom (AtomAt 'VZ as) ds, RequireAtom (AtomAt ('VS 'VZ) as) ds, LearnableAtom (AtomAt ('VS ('VS 'VZ)) as) ds)
    type Learn (Let :: (a ~> b) -> a -> b -> Type) as ds = LearnAtom (AtomAt ('VS ('VS 'VZ)) as) ds
    depKSerialize (AnyK (Proxy :: Proxy xs) (Let Refl)) = []
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ((a ~> b) -> a -> b -> Type))
        .  Require (Let :: (a ~> b) -> a -> b -> Type) as ds
        => Proxy as -> KnowledgeList ds -> ExceptT DeserializeError (State [Word8]) (AnyK (Let :: (a ~> b) -> a -> b -> Type), KnowledgeList (Learn (Let :: (a ~> b) -> a -> b -> Type) as ds))
    depKDeserialize _ kl =
        case getAtom @d @(a ~> b) @(AtomAt 'VZ as) @ds kl of
            SomeSing (f :: Sing f) ->
                case getAtom @d @a @(AtomAt ('VS 'VZ) as) @ds kl of
                    SomeSing (x :: Sing x) ->
                        case learnAtom @d @b @(AtomAt ('VS ('VS 'VZ)) as) (SomeSing (f @@ x)) kl of
                            Nothing -> throwError $ DeserializeError "Learned something contradictory while Let-binding"
                            Just kl' ->
                                return (AnyK (Proxy @(f :&&: x :&&: Apply f x :&&: 'LoT0)) (Let Refl), kl')

instance DepKDeserialize (Let f) where
    type Require (Let f) as ds = Require1Up (Let f) as ds
    type Learn (Let f) as ds = Learn1Up (Let f) as ds
    depKSerialize = depKSerialize1Up
    depKDeserialize = depKDeserialize1Up

instance DepKDeserialize (Let f x) where
    type Require (Let f x) as ds = Require1Up (Let f x) as ds
    type Learn (Let f x) as ds = Learn1Up (Let f x) as ds
    depKSerialize = depKSerialize1Up
    depKDeserialize = depKDeserialize1Up

instance DepKDeserialize (Let f x y) where
    type Require (Let f x y) as ds = Require1Up (Let f x y) as ds
    type Learn (Let f x y) as ds = Learn1Up (Let f x y) as ds
    depKSerialize = depKSerialize1Up
    depKDeserialize = depKDeserialize1Up


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


data Let2 (f :: a ~> b ~> c) (x :: a) (y :: b) (z :: c) = forall f1. Let2
    { f1 :: Let f x f1
    , z  :: Let f1 y z
    }
deriving instance Show (Let2 f x y z)
$(deriveGenericK ''Let2)
deriving instance DepKDeserialize Let2
deriving instance DepKDeserialize (Let2 f)
deriving instance DepKDeserialize (Let2 f x)
deriving instance DepKDeserialize (Let2 f x y)
deriving instance DepKDeserialize (Let2 f x y z)

data Let3 (f :: a0 ~> a1 ~> a2 ~> b) (x0 :: a0) (x1 :: a1) (x2 :: a2) (y :: b) = forall f1. Let3
    { f1 :: Let f x0 f1
    , y  :: Let2 f1 x1 x2 y
    }
deriving instance Show (Let3 f x0 x1 x2 y)
$(deriveGenericK ''Let3)
deriving instance DepKDeserialize Let3
deriving instance DepKDeserialize (Let3 f)
deriving instance DepKDeserialize (Let3 f x0)
deriving instance DepKDeserialize (Let3 f x0 x1)
deriving instance DepKDeserialize (Let3 f x0 x1 x2)
deriving instance DepKDeserialize (Let3 f x0 x1 x2 y)
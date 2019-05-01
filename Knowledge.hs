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

module Knowledge where

import DepState

import Data.Kind
import Data.Singletons
import Data.Singletons.Decide
import Data.Type.Equality
import Unsafe.Coerce

data Knowledge :: DepState -> a -> Type where
    KnowledgeU :: Knowledge 'Unknown a
    KnowledgeK :: Sing a -> Knowledge 'Known a
data Knwlg :: DepState -> Type -> Type where
    KnwlgU :: Knwlg 'Unknown a
    KnwlgK :: forall (x :: a). Sing x -> Knwlg 'Known a
deriving instance Show (Sing a) => Show (Knowledge d a)

withKnwlg :: forall d a r. Knwlg d a -> (forall (x :: a). Knowledge d x -> r) -> r
withKnwlg KnwlgU f = f KnowledgeU
withKnwlg (KnwlgK s) f = f (KnowledgeK s)

knowledgeToKnwlg :: forall d (x :: a). Knowledge d x -> Knwlg d a
knowledgeToKnwlg KnowledgeU = KnwlgU
knowledgeToKnwlg (KnowledgeK s) = KnwlgK s

sameKnowlege :: forall (d1 :: DepState) (d2 :: DepState) (x1 :: k) (x2 :: k).
    SDecide k =>
    Knowledge d1 x1 -> Knowledge d2 x2 -> Maybe (x1 :~: x2)
sameKnowlege KnowledgeU KnowledgeU = Just (unsafeCoerce Refl)  -- TODO: unsafeCoerce!! Replace with coerce??
sameKnowlege KnowledgeU (KnowledgeK s) = Just (unsafeCoerce Refl)  -- TODO: same!
sameKnowlege (KnowledgeK s) KnowledgeU = Just (unsafeCoerce Refl)  -- TODO: same!
sameKnowlege (KnowledgeK s1) (KnowledgeK s2) =
    case s1 %~ s2 of
        Proved r -> Just r
        Disproved f -> Nothing

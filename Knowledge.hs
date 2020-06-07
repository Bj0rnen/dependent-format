{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Knowledge where

import DepState

import Data.Kind
import Data.Singletons
import Data.Singletons.Decide
import Unsafe.Coerce

data Knowledge :: DepState -> a -> Type where
    KnowledgeU :: Knowledge 'Unknown a
    KnowledgeK :: Sing a -> Knowledge 'Known a
deriving instance Show (Sing a) => Show (Knowledge d a)

sameKnowlege :: forall k (d1 :: DepState) (d2 :: DepState) (x1 :: k) (x2 :: k).
    SDecide k =>
    Knowledge d1 x1 -> Knowledge d2 x2 -> Maybe (x1 :~: x2)
sameKnowlege KnowledgeU KnowledgeU = Just (unsafeCoerce Refl)  -- TODO: unsafeCoerce!! Replace with coerce??
sameKnowlege KnowledgeU (KnowledgeK s) = Just (unsafeCoerce Refl)  -- TODO: same!
sameKnowlege (KnowledgeK s) KnowledgeU = Just (unsafeCoerce Refl)  -- TODO: same!
sameKnowlege (KnowledgeK s1) (KnowledgeK s2) =
    case s1 %~ s2 of
        Proved r -> Just r
        Disproved f -> Nothing

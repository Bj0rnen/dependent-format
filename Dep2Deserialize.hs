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

module Dep2Deserialize where

import Serialize
import Vector
import DepState
import DepLevel
import Knowledge

import Data.Kind
import GHC.TypeNats
import Data.Singletons
import Data.Singletons.TypeLits
import Data.Singletons.Decide
import Exinst

import Generics.Kind hiding (Nat)

import Data.Word


data SomeDep2 :: (a -> b -> Type) -> DepState -> DepState -> Type where
    SomeDep2 :: forall d1 d2 f x y. Knowledge d1 x -> Knowledge d2 y -> f x y -> SomeDep2 f d1 d2
deriving instance (forall x y. (Show (f x y), Show (Sing x), Show (Sing y))) => Show (SomeDep2 f d1 d2)

data SomeDepStates :: [(Type, DepState)] -> Type where
    SomeDepStatesNil :: SomeDepStates '[]
    SomeDepStatesCons :: Knwlg w a -> SomeDepStates xs -> SomeDepStates ('(a, w) ': xs)
infixr `SomeDepStatesCons`

type family
    DepLevelToCtx (d :: DepLevel) (s :: DepState) :: Constraint where
    DepLevelToCtx 'Requiring s = s ~ 'Known
    DepLevelToCtx _ _ = ()

class Dep2Deserialize (f :: a -> b -> Type) where
    type DepLevel1 f (d :: DepState) :: DepState
    type DepLevel1 f (d :: DepState) = ApplyDepLevel (ActualDepLevel1 f) d
    type DepLevel2 f (d :: DepState) :: DepState
    type DepLevel2 f (d :: DepState) = ApplyDepLevel (ActualDepLevel2 f) d
    type Ctx1 f (d :: DepState) :: Constraint
    type Ctx1 f (d :: DepState) = DepLevelToCtx (ActualDepLevel1 f) d
    type Ctx2 f (d :: DepState) :: Constraint
    type Ctx2 f (d :: DepState) = DepLevelToCtx (ActualDepLevel2 f) d
    type ActualDepLevel1 f :: DepLevel
    type ActualDepLevel2 f :: DepLevel
    dep2Deserialize :: forall d1 d2. (Ctx1 f d1, Ctx2 f d2) => SomeDepStates '[ '(a, d1), '(b, d2)] -> [Word8] -> (SomeDep2 f (DepLevel1 f d1) (DepLevel2 f d2), [Word8])

deserializeSomeDep2 :: forall a b (f :: a -> b -> Type) d1 d2.
    ( Dep2Deserialize f
    , d1 ~ DepLevel1 f 'Unknown
    , d2 ~ DepLevel2 f 'Unknown
    , Ctx1 f 'Unknown
    , Ctx2 f 'Unknown
    ) => [Word8] -> (SomeDep2 f (DepLevel1 f 'Unknown) (DepLevel2 f 'Unknown), [Word8])
deserializeSomeDep2 = dep2Deserialize (KnwlgU `SomeDepStatesCons` KnwlgU `SomeDepStatesCons` SomeDepStatesNil)


someDep2ToSomeDepState2 :: forall d1 d2 a b f. SomeDep2 (f :: a -> b -> Type) d1 d2 -> SomeDepStates '[ '(a, d1), '(b, d2)]
someDep2ToSomeDepState2 (SomeDep2 KnowledgeU KnowledgeU _) = KnwlgU `SomeDepStatesCons` KnwlgU `SomeDepStatesCons` SomeDepStatesNil
someDep2ToSomeDepState2 (SomeDep2 KnowledgeU (KnowledgeK y) a) = KnwlgU `SomeDepStatesCons` (KnwlgK y) `SomeDepStatesCons` SomeDepStatesNil
someDep2ToSomeDepState2 (SomeDep2 (KnowledgeK x) KnowledgeU a) = (KnwlgK x) `SomeDepStatesCons` KnwlgU `SomeDepStatesCons` SomeDepStatesNil
someDep2ToSomeDepState2 (SomeDep2 (KnowledgeK x) (KnowledgeK y) a) = (KnwlgK x) `SomeDepStatesCons` (KnwlgK y) `SomeDepStatesCons` SomeDepStatesNil


data Prod2 (l :: a -> b -> Type) (r :: a -> b -> Type) x y = Prod2 (l x y) (r x y)
    deriving Show

newtype Curry2 f a b where
    Curry2 :: f (a :&&: b :&&: LoT0) -> Curry2 f a b

instance
    ( SDecide a, SDecide b
    , Dep2Deserialize l, Dep2Deserialize r)
    => Dep2Deserialize (Prod2 (l :: a -> b -> Type) r) where
    type DepLevel1 (Prod2 l r) d = DepLevel1 r (DepLevel1 l d)
    type DepLevel2 (Prod2 l r) d = DepLevel2 r (DepLevel2 l d)
    type Ctx1 (Prod2 l r) (d :: DepState) = (Ctx1 l d, Ctx1 r (DepLevel1 l d))
    type Ctx2 (Prod2 l r) (d :: DepState) = (Ctx2 l d, Ctx2 r (DepLevel2 l d))
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Prod2 l r) = ProductDepLevel (ActualDepLevel1 l) (ActualDepLevel1 r)
    type ActualDepLevel2 (Prod2 l r) = ProductDepLevel (ActualDepLevel2 l) (ActualDepLevel2 r)
    dep2Deserialize :: forall d1 d2. (Ctx1 (Prod2 l r) d1, Ctx2 (Prod2 l r) d2) => SomeDepStates '[ '(a, d1), '(b, d2)] -> [Word8] -> (SomeDep2 (Prod2 l r) (DepLevel1 (Prod2 l r) d1) (DepLevel2 (Prod2 l r) d2), [Word8])
    dep2Deserialize (k1 `SomeDepStatesCons` k2 `SomeDepStatesCons` SomeDepStatesNil) bs =
        case dep2Deserialize @a @b @l (k1 `SomeDepStatesCons` k2 `SomeDepStatesCons` SomeDepStatesNil) bs of
            (sdl@(SomeDep2 (k3 :: Knowledge (DepLevel1 l d1) x1_) (k4 :: Knowledge (DepLevel2 l d2) y1_) l), bs') ->
                case dep2Deserialize @a @b @r (knowledgeToKnwlg k3 `SomeDepStatesCons` knowledgeToKnwlg k4 `SomeDepStatesCons` SomeDepStatesNil) bs' of
                    (SomeDep2 (k5 :: Knowledge (DepLevel1 (Prod2 l r) d1) x2_) (k6 :: Knowledge (DepLevel2 (Prod2 l r) d2) y2_) r, bs'') ->
                        case (sameKnowlege k3 k5, sameKnowlege k4 k6) of
                            (Just Refl, Just Refl) ->
                                (SomeDep2 k5 k6 (Prod2 l r), bs'')

newtype Var2Wrapper f a b = Var2Wrapper { unwrapVar2 :: f a b }
instance (forall x y. GenericK f (x :&&: y :&&: LoT0), Dep2Deserialize (Curry2 (RepK f))) => Dep2Deserialize (Var2Wrapper f) where
    type DepLevel1 (Var2Wrapper f) d = DepLevel1 (Curry2 (RepK f)) d
    type DepLevel2 (Var2Wrapper f) d = DepLevel2 (Curry2 (RepK f)) d
    type Ctx1 (Var2Wrapper f) (d :: DepState) = (Ctx1 (Curry2 (RepK f)) d)
    type Ctx2 (Var2Wrapper f) (d :: DepState) = (Ctx2 (Curry2 (RepK f)) d)
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Var2Wrapper f) = ActualDepLevel1 (Curry2 (RepK f))
    type ActualDepLevel2 (Var2Wrapper f) = ActualDepLevel2 (Curry2 (RepK f))
    dep2Deserialize depStates bs =
        case dep2Deserialize depStates bs of
            (SomeDep2 k1 k2 (Curry2 a :: Curry2 (RepK f) x y), bs') -> (SomeDep2 k1 k2 (Var2Wrapper (toK a) :: Var2Wrapper f x y), bs')

instance Dep2Deserialize f => Dep2Deserialize (Curry2 (Field (f :$: Var0 ':@: Var1))) where
    type DepLevel1 (Curry2 (Field (f :$: Var0 ':@: Var1))) d = DepLevel1 f d
    type DepLevel2 (Curry2 (Field (f :$: Var0 ':@: Var1))) d = DepLevel2 f d
    type Ctx1 (Curry2 (Field (f :$: Var0 ':@: Var1))) (d :: DepState) = (Ctx1 f d)
    type Ctx2 (Curry2 (Field (f :$: Var0 ':@: Var1))) (d :: DepState) = (Ctx2 f d)
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Curry2 (Field (f :$: Var0 ':@: Var1))) = ActualDepLevel1 f
    type ActualDepLevel2 (Curry2 (Field (f :$: Var0 ':@: Var1))) = ActualDepLevel2 f
    dep2Deserialize depStates bs =
        case dep2Deserialize depStates bs of
            (SomeDep2 k1 k2 (a :: f x y), bs') -> (SomeDep2 k1 k2 (Curry2 (Field a)), bs')

instance
    ( SDecide a
    , SDecide b
    , (Dep2Deserialize (Curry2 l))
    , (Dep2Deserialize (Curry2 r))
    ) => Dep2Deserialize (Curry2 ((l :: LoT (a -> b -> Type) -> Type) :*: (r :: LoT (a -> b -> Type) -> Type))) where
    type DepLevel1 (Curry2 (l :*: r)) d = DepLevel1 (Prod2 (Curry2 l) (Curry2 r)) d
    type DepLevel2 (Curry2 (l :*: r)) d = DepLevel2 (Prod2 (Curry2 l) (Curry2 r)) d
    type Ctx1 (Curry2 (l :*: r)) (d :: DepState) = (Ctx1 (Prod2 (Curry2 l) (Curry2 r)) d)
    type Ctx2 (Curry2 (l :*: r)) (d :: DepState) = (Ctx2 (Prod2 (Curry2 l) (Curry2 r)) d)
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Curry2 (l :*: r)) = ActualDepLevel1 (Prod2 (Curry2 l) (Curry2 r))
    type ActualDepLevel2 (Curry2 (l :*: r)) = ActualDepLevel2 (Prod2 (Curry2 l) (Curry2 r))
    dep2Deserialize depStates bs =
        case dep2Deserialize depStates bs of
            (SomeDep2 k1 k2 (Prod2 (Curry2 x) (Curry2 y) :: (Prod2 (Curry2 l) (Curry2 r)) x y), bs') -> (SomeDep2 k1 k2 (Curry2 (x :*: y)), bs')

data Select1of2 :: (a -> Type) -> a -> b -> Type where
    Select1of2 :: f x -> Select1of2 f x y
--instance Serialize ? => Dep2Deserialize (Select1of2 t :: a -> b -> Type) where
--    type ActualDepLevel1 (Select1of2 t :: a -> b -> Type) = DepLevelOf t
--    type ActualDepLevel2 (Select1of2 t :: a -> b -> Type) = 'NonDep
--    dep2Deserialize (k1 `SomeDepStatesCons` k2 `SomeDepStatesCons` SomeDepStatesNil) bs =
--        case deserialize @? bs of
--            (? a, bs') ->
--                withKnwlg k2 $ \k2' -> (SomeDep2 ? k2' (Select1of2 a), bs')
instance (SingKind a, Serialize (Demote a)) => Dep2Deserialize (Select1of2 Sing :: a -> b -> Type) where
    type ActualDepLevel1 (Select1of2 Sing :: a -> b -> Type) = 'Learning
    type ActualDepLevel2 (Select1of2 Sing :: a -> b -> Type) = 'NonDep
    dep2Deserialize (_ `SomeDepStatesCons` k2 `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize bs of
            (Some1 s a, bs') ->
                withKnwlg k2 $ \k2' -> (SomeDep2 (KnowledgeK s) k2' (Select1of2 a), bs')
instance Serialize t => Dep2Deserialize (Select1of2 (Vector t) :: Nat -> b -> Type) where
    type ActualDepLevel1 (Select1of2 (Vector t) :: Nat -> b -> Type) = 'Requiring
    type ActualDepLevel2 (Select1of2 (Vector t) :: Nat -> b -> Type) = 'NonDep
    dep2Deserialize (KnwlgK (SNat :: Sing x) `SomeDepStatesCons` k2 `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize @(Vector t x) bs of
            (a, bs') ->
                withKnwlg k2 $ \k2' -> (SomeDep2 (KnowledgeK SNat) k2' (Select1of2 a), bs')
instance Dep2Deserialize (Select1of2 t :: a -> b -> Type) => Dep2Deserialize (Curry2 (Field ((t :: a -> Type) :$: Var0 :: Atom (a -> b -> Type) Type))) where
    type DepLevel1 (Curry2 (Field ((t :: a -> Type) :$: Var0 :: Atom (a -> b -> Type) Type))) d = DepLevel1 (Select1of2 t :: a -> b -> Type) d
    type DepLevel2 (Curry2 (Field ((t :: a -> Type) :$: Var0 :: Atom (a -> b -> Type) Type))) d = DepLevel2 (Select1of2 t :: a -> b -> Type) d
    type Ctx1 (Curry2 (Field ((t :: a -> Type) :$: Var0 :: Atom (a -> b -> Type) Type))) (d :: DepState) = Ctx1 (Select1of2 t :: a -> b -> Type) d
    type Ctx2 (Curry2 (Field ((t :: a -> Type) :$: Var0 :: Atom (a -> b -> Type) Type))) (d :: DepState) = Ctx2 (Select1of2 t :: a -> b -> Type) d
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Curry2 (Field ((t :: a -> Type) :$: Var0 :: Atom (a -> b -> Type) Type))) = ActualDepLevel1 (Select1of2 t :: a -> b -> Type)
    type ActualDepLevel2 (Curry2 (Field ((t :: a -> Type) :$: Var0 :: Atom (a -> b -> Type) Type))) = ActualDepLevel2 (Select1of2 t :: a -> b -> Type)
    dep2Deserialize depStates bs =
        case dep2Deserialize depStates bs of
            (SomeDep2 k1 k2 (Select1of2 a), bs') ->
                (SomeDep2 k1 k2 (Curry2 (Field a)), bs')


data Visibility a = Exposed a | Hidden
type family
    Knowledge'' (s :: Visibility k) (a :: k) :: Constraint where
    Knowledge'' 'Hidden a = SingI a
    Knowledge'' ('Exposed a) b = a ~ b
data SomeDep2'' :: (a -> b -> Type) -> Visibility a -> Visibility b -> Type where
    SomeDep2'' :: forall d1 d2 f x y. (Knowledge'' d1 x, Knowledge'' d2 y) => f x y -> SomeDep2'' f d1 d2
deriving instance (forall a b. Show (f a b)) => Show (SomeDep2'' f d1 d2)


--type family
--    Visibility' (d :: DepLevel) (x :: a) :: Visibility a where
--    Visibility' 'Requiring x = 'Exposed x
--    Visibility' 'NonDep x = 'Exposed x
--    Visibility' 'Learning x = 'Hidden
--type family
--    Knowledge' (d :: DepLevel) (x :: a) :: Constraint where
--    Knowledge' 'Requiring x = SingI x
--    Knowledge' 'NonDep x = ()
--    Knowledge' 'Learning x = ()
----type family
----    Foo1 (d :: DepLevel) (a :: Type) :: Type where
----    Foo1 'Requiring (SomeDep2'' ('Hidden :: Visibility a) v2 f, [Word8]) = forall (x :: a). Sing x -> (SomeDep2'' ('Exposed x) v2 f, [Word8])
----    Foo1 'NonDep    (SomeDep2'' ('Hidden :: Visibility a) v2 f, [Word8]) = forall (x :: a).           (SomeDep2'' ('Exposed x) v2 f, [Word8])
----    Foo1 'Learning a = a
----type family
----    Foo2 (d :: DepLevel) (a :: Type) :: Type where
----    Foo2 'Requiring (SomeDep2'' v1 ('Hidden :: Visibility b) f, [Word8]) = forall (y :: b). Sing y -> (SomeDep2'' v1 ('Exposed y) f, [Word8])
----    Foo2 'NonDep    (SomeDep2'' v1 ('Hidden :: Visibility b) f, [Word8]) = forall (y :: b).           (SomeDep2'' v1 ('Exposed y) f, [Word8])
----    Foo2 'Learning a = a
----type family
----    Foo (d1 :: DepLevel) (d2 :: DepLevel) (f :: a -> b -> Type) (r :: Type) :: Type where
----    Foo 'Requiring 'Requiring (f :: a -> b -> Type) r = (forall (x :: a) (y :: b). Sing x -> Sing y -> SomeDep2'' f ('Exposed x) ('Exposed y) -> r) -> r
--class Dep2Deserialize (f :: a -> b -> Type) where
--    type DepLevel1 f :: DepLevel
--    type DepLevel2 f :: DepLevel
--    --dep2deserialize :: forall x y. (Knowledge' (DepLevel1 f) x, Knowledge' (DepLevel2 f) y) => [Word8] -> (SomeDep2'' (Visibility' (DepLevel1 f) x) (Visibility' (DepLevel2 f) y) f, [Word8])
--    --dep2deserialize :: [Word8] -> Foo1 (DepLevel1 f) (Foo2 (DepLevel2 f) (SomeDep2'' 'Hidden 'Hidden f, [Word8]))
--    dep2deserialize :: [Word8] -> forall (x :: a). Sing x -> (forall (y :: b). Sing y -> (SomeDep2'' f ('Exposed x) ('Exposed y), [Word8]))

--instance (Dep2Deserialize l, Dep2Deserialize r) => Dep2Deserialize (Prod2 l r) where
--    type DepLevel1 (Prod2 l r) = ProductDepLevel (DepLevel1 l) (DepLevel1 r)
--    --dep2deserialize :: forall x y. (Knowledge' (DepLevel1 (Prod2 l r)) x, Knowledge' (DepLevel2 (Prod2 l r)) y) => [Word8] -> (SomeDep2'' (Visibility' (DepLevel1 (Prod2 l r)) x) (Visibility' (DepLevel2 (Prod2 l r)) y) (Prod2 l r), [Word8])
--    dep2deserialize bs = undefined
--        --case deserialize @(SomeDep2'' (Visibility1 l x) (Visibility2 l y) l) bs of
--        --    (SomeDep2'' a, bs') ->
--        --        (undefined, bs')

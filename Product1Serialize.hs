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

module Product1Serialize where

import Serialize
import DepLevel

import Data.Kind
import GHC.TypeLits
import Data.Singletons
import Data.Singletons.TypeLits
import Data.Singletons.Decide
import Exinst
import Data.Coerce
import Data.Constraint

import qualified GHC.Generics as GHC
import Generics.Kind hiding (Nat)

import Data.Word


class (ldep ~ DepLevelOf l, rdep ~ DepLevelOf r) => Product1Serialize (ldep :: DepLevel) (rdep :: DepLevel) (l :: k -> Type) (r :: k -> Type) where
    p1serialize :: Some1 (l GHC.:*: r) -> [Word8]
    p1deserialize :: [Word8] -> (Some1 (l GHC.:*: r), [Word8])

-- Negative cases:
-- TODO: Could recurse down to first "Requiring" field, for a considerably nicer error message.
instance (DepLevelOf l ~ 'Requiring, DepLevelOf r ~ dlr,
    TypeError (Text "Can't deserialize a "
               :<>: ShowType l
               :<>: Text " before the type index (of kind "
               :<>: ShowType k
               :<>: Text ") is known.")
    ) => Product1Serialize 'Requiring dlr (l :: k -> Type) r where
    p1serialize = error "unreachable"
    p1deserialize = error "unreachable"
-- TODO: Could recurse down to first "Requiring" field, for a considerably nicer error message.
instance (DepLevelOf l ~ 'NonDep, DepLevelOf r ~ 'Requiring,
    TypeError (Text "Can't deserialize a "
                :<>: ShowType r
                :<>: Text " before the type index (of kind "
                :<>: ShowType k
                :<>: Text ") is known.")
    ) => Product1Serialize 'NonDep 'Requiring (l :: k -> Type) r where
    p1serialize = error "unreachable"
    p1deserialize = error "unreachable"
-- TODO: Can this case even possibly be hit?
instance (DepLevelOf l ~ 'NonDep, DepLevelOf r ~ 'NonDep,
    TypeError (Text "Can't learn type index (of kind "
                :<>: ShowType k
                :<>: Text ") from deserializing either of "
                :<>: ShowType l
                :<>: Text "or "
                :<>: ShowType r)
    ) => Product1Serialize 'NonDep 'NonDep (l :: k -> Type) r where
    p1serialize = error "unreachable"
    p1deserialize = error "unreachable"

-- TODO: Shame this generalized instance below doesn't quite get us all the way where we want to get.
-- TODO: See Trac #14937.
--instance
--    ( 'Learning ~ DepLevelOf l
--    , Serialize (Some1 l)
--    , 'Requiring ~ DepLevelOf r
--    , forall (x :: k). SingI x => Serialize (r x)
--    )
--    => Product1Serialize 'Learning 'Requiring (l :: k -> Type) (r :: k -> Type) where
--    p1serialize (Some1 (s :: Sing a) (a GHC.:*: b)) = serialize (Some1 s a) ++ (withSingI s $ serialize b)
--    p1deserialize bs =
--        case deserialize bs of
--            (Some1 (s :: Sing a) a, bs') ->
--                case withSingI s $ deserialize bs' of
--                    (b, bs'') ->
--                        (Some1 s (a GHC.:*: b), bs'')

--instance
--    ( 'Learning ~ DepLevelOf l
--    , Serialize (Some1 l)
--    , 'Requiring ~ DepLevelOf r
--    , forall (x :: Nat). KnownNat x => Serialize (r x)
--    )
--    => Product1Serialize 'Learning 'Requiring (l :: Nat -> Type) (r :: Nat -> Type) where
--    p1serialize (Some1 (SNat :: Sing a) (a GHC.:*: b)) = serialize (Some1 SNat a) ++ serialize b
--    p1deserialize bs =
--        case deserialize bs of
--            (Some1 (SNat :: Sing a) a, bs') ->
--                case deserialize bs' of
--                    (b, bs'') ->
--                        (Some1 SNat (a GHC.:*: b), bs'')

instance (forall x. KnownNat x => c (f x)) => Dict1 c (f :: Nat -> Type) where
    dict1 SNat = Dict
instance
    ( 'Learning ~ DepLevelOf l
    , Serialize (Some1 l)
    , 'Requiring ~ DepLevelOf r
    , Dict1 Serialize r
    )
    => Product1Serialize 'Learning 'Requiring (l :: k -> Type) (r :: k -> Type) where
    p1serialize (Some1 (s :: Sing a) (a GHC.:*: b)) = serialize (Some1 s a) ++ (withDict @(Serialize (r a)) (dict1 s) $ serialize b)
    p1deserialize bs =
        case deserialize bs of
            (Some1 (s :: Sing a) a, bs') ->
                case withDict @(Serialize (r a)) (dict1 s) $ deserialize bs' of
                    (b, bs'') ->
                        (Some1 s (a GHC.:*: b), bs'')
instance
    ( 'Learning ~ DepLevelOf l
    , Serialize (Some1 l)
    , 'Learning ~ DepLevelOf r
    , Serialize (Some1 r)
    , SDecide t
    , SingKind t
    , Show (Demote t)
    )
    => Product1Serialize 'Learning 'Learning (l :: t -> Type) r where
    p1serialize (Some1 (s :: Sing a) (a GHC.:*: b)) = serialize (Some1 s a) ++ serialize (Some1 s b)
    p1deserialize bs =
        case deserialize bs of
            (Some1 s1 (a :: l a1), bs') ->
                case deserialize bs' of
                    (Some1 s2 (b :: r a2), bs'') ->
                        case s1 %~ s2 of
                            Proved Refl -> (Some1 s1 (a GHC.:*: b), bs'')
                            -- TODO: deserialize should return Either.
                            -- TODO: Should I wrap in SomeSing before showing instead of demoting?
                            Disproved r -> error ("((Sing) Refuted: " ++ show (withSingI s1 $ demote @a1) ++ " %~ " ++ show (withSingI s2 $ demote @a2) ++ ")")
instance
    ( 'NonDep ~ DepLevelOf l
    , forall x. Serialize (l x), forall x y. Coercible (l x) (l y)
    , 'Learning ~ DepLevelOf r
    , Serialize (Some1 r)
    )
    => Product1Serialize 'NonDep 'Learning (l :: t -> Type) r where
    p1serialize (Some1 (s :: Sing a) (a GHC.:*: b)) = serialize a ++ serialize (Some1 s b)
    p1deserialize bs =
        case deserialize bs of
            (a, bs') ->
                case deserialize bs' of
                    (Some1 (s :: Sing a) (b :: r a), bs'') ->
                        (Some1 s (coerce @(l _) a GHC.:*: b), bs'')
instance
    ( 'Learning ~ DepLevelOf l
    , Serialize (Some1 l)
    , 'NonDep ~ DepLevelOf r
    , forall x. Serialize (r x)  -- We don't need it, but it might be consistent to also have: forall x y. Coercible (r x) (r y)
    )
    => Product1Serialize 'Learning 'NonDep (l :: t -> Type) r where
    p1serialize (Some1 (s :: Sing a) (a GHC.:*: b)) = serialize (Some1 s a) ++ serialize b
    p1deserialize bs =
        case deserialize bs of
            (Some1 (s :: Sing a) (a :: l a), bs') ->
                case deserialize bs' of
                    (b :: r a, bs'') ->
                        (Some1 s (a GHC.:*: b), bs'')

--instance (Product1Serialize (DepLevelOf f) (DepLevelOf g) f g) => Serialize (Some1 (f GHC.:*: g)) where
--    serialize a = p1serialize @_ @(DepLevelOf f) @(DepLevelOf g) a
--    deserialize bs = p1deserialize @_ @(DepLevelOf f) @(DepLevelOf g) bs
instance {-# OVERLAPPABLE #-} (Product1Serialize (DepLevelOf f) (DepLevelOf g) f g) => Serialize (Some1 (f GHC.:*: g)) where
    serialize a = p1serialize @_ @(DepLevelOf f) @(DepLevelOf g) a
    deserialize bs = p1deserialize @_ @(DepLevelOf f) @(DepLevelOf g) bs

instance {-# OVERLAPS #-} (Product1Serialize (DepLevelOf f) (DepLevelOf g) f g) => Serialize (Some1 ((f :: LoT (a -> Type) -> Type) GHC.:*: g)) where
    serialize a = p1serialize @_ @(DepLevelOf f) @(DepLevelOf g) a
    deserialize bs = p1deserialize @_ @(DepLevelOf f) @(DepLevelOf g) bs

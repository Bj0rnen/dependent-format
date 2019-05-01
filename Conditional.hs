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

module Conditional where

import Serialize

import Data.Kind
import Data.Singletons
import Data.Singletons.Decide

import Generics.Kind hiding ((:~:))

import Data.Word

import Unsafe.Coerce


data Conditional :: Bool -> Type -> Type where
    None ::      Conditional 'False a
    Some :: a -> Conditional 'True  a
deserializeSing'
    :: forall k i b vars.
       (SingKind k, SDecide k, Serialize (Demote k))
    => Conditional b (Sing (Interpret (Var i) vars))
    -> [Word8]
    -> (Field (Kon (Sing :: k -> Type) :@: Var i) vars, [Word8], Conditional 'True (Sing (Interpret (Var i) vars)))
deserializeSing' None bs =
    case deserialize bs of
        (FromSing (x :: Sing x), bs') ->
            case unsafeCoerce Refl :: (Interpret (Var i) vars) :~: x of
                Refl ->
                    (Field x, bs', Some x)
deserializeSing' (Some a) bs =
    case deserialize bs of
        (FromSing (x :: Sing x), bs') ->
            case a %~ x of
                Proved Refl -> (Field x, bs', Some a)
                Disproved r -> error "Learned something contradictory"  -- Or: error ("((Sing) Refuted: " ++ show (withSingI (sing @(Interpret (Var VZ) vars)) $ demote @(Interpret (Var VZ) vars)) ++ " %~ " ++ show (withSingI s $ demote @size1) ++ ")")


--deserializeSing' ::
--    forall k v (vars :: LoT ks) bs r.
--    (SingKind k, SDecide k, Serialize (Demote k)) =>
--    PartialSings ks bs ->
--    (Sing (Interpret (Var v) vars) -> (Field (Kon (Sing :: k -> Type) :@: Var v) vars, [Word8]) -> r) ->
--    [Word8] ->
--    r
--deserializeSing' Nothing f bs =
--    case deserialize bs of
--        (FromSing (s :: Sing x), bs') ->
--            case unsafeCoerce Refl :: (Interpret (Var v) vars) :~: x of
--                Refl ->
--                    f s (Field s, bs')
--deserializeSing' (Just a) f bs =
--    case deserialize bs of
--        (FromSing s, bs') ->
--            case a %~ s of
--                Proved Refl -> f s (Field s, bs')
--                Disproved r -> error "Learned something contradictory"  -- Or: error ("((Sing) Refuted: " ++ show (withSingI (sing @(Interpret (Var VZ) vars)) $ demote @(Interpret (Var VZ) vars)) ++ " %~ " ++ show (withSingI s $ demote @size1) ++ ")")

class ConditionalSingIConstraint s a => ConditionalSingI (s :: Bool) (a :: k) where
    type ConditionalSingIConstraint s a :: Constraint
    maybeSameType :: Sing x -> Decision (a :~: x)
instance (SDecide k, SingI (a :: k)) => ConditionalSingI 'True a where
    type ConditionalSingIConstraint 'True a = (SDecide k, SingI (a :: k))
    maybeSameType s = sing @a %~ s
instance ()      => ConditionalSingI 'False a where
    type ConditionalSingIConstraint 'False a = ()
    maybeSameType (s :: Sing x) = Proved (unsafeCoerce Refl :: a :~: x)  -- TODO: unsafeCoerce!!


data PartialSings :: Type -> [Bool] -> Type where
    PartialSings0 ::                                        PartialSings Type '[]
    MisSing       ::                  PartialSings ks bs -> PartialSings (k -> ks) ('False ': bs)
    (:&&+:)       :: Sing (a :: k) -> PartialSings ks bs -> PartialSings (k -> ks) ('True  ': bs)

type family InterpretPartialSings (t :: Atom ks k) (tys :: PartialSings ks bs) :: Maybe (Sing (a :: k))
    where
        InterpretPartialSings ('Var 'VZ) (t ':&&+: ts) = 'Just t
        InterpretPartialSings ('Var ('VS v)) (t ':&&+: ts) = InterpretPartialSings ('Var v) ts
        InterpretPartialSings ('Var 'VZ) (MisSing ts) = 'Nothing
        InterpretPartialSings ('Var ('VS v)) (MisSing ts) = InterpretPartialSings ('Var v) ts
        --InterpretPartialSings ('Kon t) tys = t
        --InterpretPartialSings (f ':@: x) tys = InterpretPartialSings f tys (InterpretPartialSings x tys)
        --InterpretPartialSings (c ':&: d2) tys = (InterpretPartialSings c tys, InterpretPartialSings d2 tys)
        --InterpretPartialSings ('ForAll f) tys = ForAllI f tys
        --InterpretPartialSings (c ':=>>: f) tys = SuchThatI c f tys

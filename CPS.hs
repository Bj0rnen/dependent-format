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

module CPS where

import Data.Singletons
import Data.Constraint


-- TODO: How do we implement something like this, in a way that breaks it down structurally?
-- TODO: We already have an issue: we can't pass `vars` from the outside.
-- TODO: Is something like `PartiallyKnown` the way? Or maybe RankNTypes, CPS?
deserializeThis :: [Word8] ->
    ( ((Field (Kon Sing :@: Var VZ) :*: Field (Kon Sing :@: Var (VS VZ)))
        :*:
       (Field (Kon Vector :@: Kon Word8 :@: Var VZ) :*: Field (Kon Vector :@: Kon Word8 :@: Var (VS VZ))))
      vars
    , [Word8])
deserializeThis bs = undefined


class MaybeSingI (a :: k) where
    maybeSameType' :: forall x. Sing x -> Decision (a :~: x)
-- Here be dragons
-- TODO: Plenty of unsafeCoerce here. Maybe unavoidable, but needs to be rigorously verified.
newtype DI (a :: k) = Don'tInstantiate (MaybeSingI a => Dict (MaybeSingI a))
noSingI :: forall k (a :: k). Dict (MaybeSingI a)
noSingI = withMaybeSingI Dict
    where
        withMaybeSingI :: (MaybeSingI a => Dict (MaybeSingI a)) -> Dict (MaybeSingI a)
        withMaybeSingI d = unsafeCoerce (Don'tInstantiate d) ((\(s :: Sing x) -> Proved (unsafeCoerce Refl :: a :~: x)) :: forall x. Sing x -> Decision (a :~: x))
yesSingI :: forall k (a :: k). SDecide k => Sing a -> Dict (MaybeSingI a)
yesSingI s = withMaybeSingI Dict
    where
        withMaybeSingI :: (MaybeSingI a => Dict (MaybeSingI a)) -> Dict (MaybeSingI a)
        withMaybeSingI d = unsafeCoerce (Don'tInstantiate d) ((\x -> s %~ x) :: forall x. Sing x -> Decision (a :~: x))

deserializeSing ::
    forall k v vars r.
    MaybeSingI (Interpret (Var v) vars) =>
    (SingKind k, SDecide k, Serialize (Demote k)) =>
    (forall vars'. (SingI (Interpret (Var v) vars'), MaybeSingI (Interpret (Var v) vars'), vars ~ vars') => (Field (Kon (Sing :: k -> Type) :@: Var v) vars', [Word8], Proxy vars') -> r) ->
    [Word8] ->
    r
deserializeSing f bs =
    case deserialize bs of
        (FromSing s, bs') ->
            case maybeSameType' @k @(Interpret (Var v) vars) s of
                Proved Refl -> withDict (yesSingI @k @(Interpret (Var v) vars) s) $ withSingI s $ f @vars (Field s, bs', Proxy)
                Disproved r -> error "Learned something contradictory"  -- Or: error ("((Sing) Refuted: " ++ show (withSingI (sing @(Interpret (Var VZ) vars)) $ demote @(Interpret (Var VZ) vars)) ++ " %~ " ++ show (withSingI s $ demote @size1) ++ ")")

deserializeVector :: forall v vars. ConditionalSingI 'True (Interpret (Var v) vars) =>
    forall r.
    ((Field (Kon Vector :@: Kon Word8 :@: Var v) vars, [Word8]) -> r) ->
    [Word8] ->
    r
deserializeVector f bs =
    case deserialize bs of
        (arr, bs') ->
            f (Field arr, bs')

nth :: forall (n :: Nat). KnownNat n => Demote Nat -> Vector Word8 n -> Maybe Word8
nth _ Nil = Nothing
nth (FromSing (SNat :: Sing i)) (x :> xs :: Vector Word8 n) =
    case ltNat @i @n of
        Nothing -> Nothing
        Just Refl -> ifZeroElse @i (Just x) $ \(Proxy :: Proxy i') ->
            nth @(n - 1) (demote @i') xs \\ subNat @n @1 \\ addNonZero @n @1 \\ predecessor @n

useDeserializeSingNoSingI :: forall (vars :: LoT (Nat -> Type)). Demote Nat
useDeserializeSingNoSingI = withDict (noSingI @Nat @(Interpret ('Var 'VZ) vars)) $ deserializeSing @Nat @'VZ @vars (\(Field s, bs, Proxy) -> FromSing s) [2, 2, 3, 4]
useDeserializeSingYesSingIOK :: forall (vars :: LoT (Nat -> Type)). vars ~ (2 :&&: LoT0) => Demote Nat
useDeserializeSingYesSingIOK = withDict (yesSingI @Nat @(Interpret ('Var 'VZ) vars) (SNat @2)) $ deserializeSing @Nat @'VZ @vars (\(Field s, bs, Proxy) -> FromSing s) [2, 2, 3, 4]
useDeserializeSingYesSingIContradictory :: forall (vars :: LoT (Nat -> Type)). vars ~ (3 :&&: LoT0) => Demote Nat
useDeserializeSingYesSingIContradictory = withDict (yesSingI @Nat @(Interpret ('Var 'VZ) vars) (SNat @3)) $ deserializeSing @Nat @'VZ @vars (\(Field s, bs, Proxy) -> FromSing s) [2, 2, 3, 4]


useDeserializeVector0 :: Maybe Word8
useDeserializeVector0 = deserializeVector @'VZ @(2 :&&: LoT0) (\(Field xs, bs) -> nth 1 xs) [2, 3, 4]
deserializeThisCPS
    :: forall vars r.
       ( ( ( ( (Field (Kon Sing :@: Var VZ)                 :*: Field (Kon Sing :@: Var (VS VZ)))
             :*:
               (Field (Kon Vector :@: Kon Word8 :@: Var VZ) :*: Field (Kon Vector :@: Kon Word8 :@: Var (VS VZ)))
             ) vars
           , [Word8]
           )
         -> r
         )
       )
    -> [Word8]
    -> r
deserializeThisCPS f bs =
    withDict (noSingI @Nat @(Interpret ('Var 'VZ) vars)) $
    withDict (noSingI @Nat @(Interpret ('Var ('VS 'VZ)) vars)) $
    deserializeSing @Nat @'VZ @vars (\(a, bs', Proxy :: Proxy vars') ->
        deserializeSing @Nat @('VS 'VZ) @vars' (\(b, bs'', Proxy :: Proxy vars'') ->
            deserializeVector @'VZ @vars'' (\(c, bs''') ->
                deserializeVector @('VS 'VZ) @vars'' (\(d, bs'''') ->
                    f ((a :*: b) :*: (c :*: d), bs'''')) bs''') bs'') bs') bs

deserializeSingVZTwice
    :: forall vars r.
       ( ( ( ( (Field (Kon Sing :@: Var VZ)                 :*: Field (Kon Sing :@: Var (VS VZ)))
             :*:
               (Field (Kon Vector :@: Kon Word8 :@: Var VZ) :*: Field (Kon Vector :@: Kon Word8 :@: Var (VS VZ)))
             ) vars
           , [Word8]
           )
         -> r
         )
       )
    -> [Word8]
    -> r
deserializeSingVZTwice f bs =
    withDict (noSingI @Nat @(Interpret ('Var 'VZ) vars)) $
    withDict (noSingI @Nat @(Interpret ('Var ('VS 'VZ)) vars)) $
    deserializeSing @Nat @'VZ @vars (\(a, bs', Proxy :: Proxy vars') ->
        deserializeSing @Nat @'VZ @vars' (\(a', bs'', Proxy :: Proxy vars'') ->
            deserializeSing @Nat @('VS 'VZ) @vars'' (\(b, bs''', Proxy :: Proxy vars''') ->
                deserializeVector @'VZ @vars''' (\(c, bs'''') ->
                    deserializeVector @('VS 'VZ) @vars''' (\(d, bs''''') ->
                        f ((a :*: b) :*: (c :*: d), bs''''')) bs'''') bs''') bs'') bs') bs

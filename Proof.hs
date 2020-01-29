{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Proof where

import Data.Type.Equality
import Data.Proxy
import Data.Kind
import Unsafe.Coerce

axm :: forall a b r. (a ~ b => r) -> r
axm x =
    case unsafeCoerce (Refl @a) of
        (Refl :: a :~: b) -> x

letT :: forall a r. (forall b. a ~ b => Proxy b -> r) -> r
letT f = f Proxy

type family
    AllSame (xs :: [k]) :: Constraint where
    AllSame '[] = ()
    AllSame (x ': '[]) = ()
    AllSame (x ': y ': xs) = (x ~ y, AllSame (y ': xs))

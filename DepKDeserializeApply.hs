{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
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

module DepKDeserializeApply where

import Control.Monad.Indexed
import Control.Monad.Indexed.State
import Data.Kind
import Data.Singletons
import Data.Singletons.Prelude.Maybe
import Data.Type.Equality
import Data.Word
import DepKDeserialize
import Generics.Kind hiding ((:~:))
import Generics.Kind.TH

import DepKDeserializeLet

data App :: (b -> Type) -> (a ~> b) -> a -> Type where
    App :: forall c f x fx.
        { fx  :: Let f x fx
        , cfx :: c fx
        } -> App c f x
--data App :: (b -> Type) -> (a ~> b) -> a -> Type where
--    App :: c (f @@ x) -> App c f x

--deriving instance (fx ~ (f @@ x), Show (c fx)) => Show (App c f x)
$(deriveGenericK ''App)
--instance DepKDeserialize (App :: (b -> Type) -> (a ~> b) -> a -> Type) where
--    type Require (App :: (b -> Type) -> (a ~> b) -> a -> Type) (as :: AtomList d ((b -> Type) -> (a ~> b) -> a -> Type)) (ds :: DepStateList d) =
--        RequireK (RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type)) as ds
--    type Learn (App :: (b -> Type) -> (a ~> b) -> a -> Type) (as :: AtomList d ((b -> Type) -> (a ~> b) -> a -> Type)) (ds :: DepStateList d) =
--        LearnK (RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type)) as ds
--    depKSerialize
--        :: forall d (ds :: DepStateList d) (as :: AtomList d ((b -> Type) -> (a ~> b) -> a -> Type)) (xs :: LoT ((b -> Type) -> (a ~> b) -> a -> Type))
--        .  ( GenericK (App :: (b -> Type) -> (a ~> b) -> a -> Type)
--           , DepKDeserializeK (RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type))
--           , RequireK (RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type)) as ds
--           , Learn (App :: (b -> Type) -> (a ~> b) -> a -> Type) as ds ~ LearnK (RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type)) as ds)
--        => Proxy as
--        -> TheseK (App :: (b -> Type) -> (a ~> b) -> a -> Type) xs
--        -> IxState (KnowledgeList ds) (KnowledgeList (Learn (App :: (b -> Type) -> (a ~> b) -> a -> Type) as ds)) [Word8]
--    depKSerialize p (TheseK (Proxy :: Proxy xs) a) =
--        depKSerializeK p (fromK @_ @(App :: (b -> Type) -> (a ~> b) -> a -> Type) @xs a :: RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type) xs)
--    --depKDeserialize
--    --    :: forall d (ds :: DepStateList d) (as :: AtomList d ((b -> Type) -> (a ~> b) -> a -> Type))
--    --    .  (GenericK (App :: (b -> Type) -> (a ~> b) -> a -> Type), DepKDeserializeK (RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type)), RequireK (RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type)) as ds, Learn (App :: (b -> Type) -> (a ~> b) -> a -> Type) as ds ~ LearnK (RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type)) as ds)
--    --    => Proxy as -> IxGet ds (Learn (App :: (b -> Type) -> (a ~> b) -> a -> Type) as ds) (AnyK (App :: (b -> Type) -> (a ~> b) -> a -> Type))
--    --depKDeserialize p =
--    --    depKDeserializeK @_ @(RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type)) p >>>= \(AnyKK (r :: RepK (App :: (b -> Type) -> (a ~> b) -> a -> Type) xs)) ->
--    --    ireturn $ AnyK (Proxy @xs) (toK @_ @(App :: (b -> Type) -> (a ~> b) -> a -> Type) @xs r)

deriving instance DepKDeserialize c => DepKDeserialize (App c)
deriving instance DepKDeserialize c => DepKDeserialize (App c f)
deriving instance DepKDeserialize c => DepKDeserialize (App c f x)

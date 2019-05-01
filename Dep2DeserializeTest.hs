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

module Dep2DeserializeTest where

import Dep2Deserialize

import Serialize
import Vector
import DepState
import DepLevel
import Knowledge

import Data.Kind
import GHC.TypeNats
import Data.Singletons
import Data.Singletons.TypeLits
import Exinst
import Data.Type.Equality

import qualified GHC.Generics as GHC
import Generics.Kind hiding (Nat)

import Data.Word
import Numeric.Natural


data RR (size1 :: Nat) (size2 :: Nat) = RR
    { arr1  :: Vector Word8 size1
    , arr2  :: Vector Word8 size2
    } deriving (Show, GHC.Generic)
instance (SingI x, SingI y) => Serialize (SomeDep2'' RR ('Exposed x) ('Exposed y)) where
    serialize (SomeDep2'' (RR arr1 arr2)) = serialize arr1 ++ serialize arr2
    deserialize bs =
        case deserialize bs of
            (arr1, bs') ->
                case deserialize bs' of
                    (arr2, bs'') ->
                        (SomeDep2'' (RR arr1 arr2), bs'')

data RN (size1 :: Nat) (size2 :: Nat) = RN
    { arr1  :: Vector Word8 size1
    } deriving (Show, GHC.Generic)
instance SingI x => Serialize (SomeDep2'' RN ('Exposed x) ('Exposed y)) where
    serialize (SomeDep2'' (RN arr1)) = serialize arr1
    deserialize bs =
        case deserialize bs of
            (arr1, bs') ->
                (SomeDep2'' (RN arr1), bs')

data RL (size1 :: Nat) (size2 :: Nat) = RL
    { arr1  :: Vector Word8 size1
    , size2 :: Sing size2
    } deriving (Show, GHC.Generic)
instance KnownNat x => Serialize (SomeDep2'' RL ('Exposed x) 'Hidden) where
    serialize (SomeDep2'' (RL arr1 size2)) = serialize arr1 ++ serialize size2
    deserialize bs =
        case deserialize bs of
            (arr1, bs') ->
                case deserialize bs' of
                    (Some1 SNat size2, bs'') ->
                        (SomeDep2'' (RL arr1 size2), bs'')

data NR (size1 :: Nat) (size2 :: Nat) = NR
    { arr2  :: Vector Word8 size2
    } deriving (Show, GHC.Generic)
instance KnownNat y => Serialize (SomeDep2'' NR ('Exposed x) ('Exposed y)) where
    serialize (SomeDep2'' (NR arr2)) = serialize arr2
    deserialize bs =
        case deserialize bs of
            (arr2, bs') ->
                (SomeDep2'' (NR arr2), bs')

data NN (size1 :: Nat) (size2 :: Nat) = NN
    {} deriving (Show, GHC.Generic)
instance Serialize (SomeDep2'' NN ('Exposed x) ('Exposed y)) where
    serialize (SomeDep2'' NN) = []
    deserialize bs =
        (SomeDep2'' NN, bs)

data NL (size1 :: Nat) (size2 :: Nat) = NL
    { size2 :: Sing size2
    } deriving (Show, GHC.Generic)
instance Serialize (SomeDep2'' NL ('Exposed x) 'Hidden) where
    serialize (SomeDep2'' (NL size2)) = serialize size2
    deserialize bs =
        case deserialize bs of
            (Some1 SNat size2, bs') ->
                (SomeDep2'' (NL size2), bs')

data LR (size1 :: Nat) (size2 :: Nat) = LR
    { size1 :: Sing size1
    , arr2  :: Vector Word8 size2
    } deriving (Show, GHC.Generic)
instance SingI y => Serialize (SomeDep2'' LR 'Hidden ('Exposed y)) where
    serialize (SomeDep2'' (LR size1 arr2)) = serialize size1 ++ serialize arr2
    deserialize bs =
        case deserialize bs of
            (Some1 SNat size1, bs') ->
                case deserialize bs' of
                    (arr2, bs'') ->
                        (SomeDep2'' (LR size1 arr2), bs'')

data LN (size1 :: Nat) (size2 :: Nat) = LN
    { size1 :: Sing size1
    } deriving (Show, GHC.Generic)
instance Serialize (SomeDep2'' LN 'Hidden ('Exposed y)) where
    serialize (SomeDep2'' (LN size1)) = serialize size1
    deserialize bs =
        case deserialize bs of
            (Some1 SNat size1, bs') ->
                (SomeDep2'' (LN size1), bs')

data LL (size1 :: Nat) (size2 :: Nat) = LL
    { size1 :: Sing size1
    , size2 :: Sing size2
    } deriving (Show, GHC.Generic)
instance Serialize (SomeDep2'' LL 'Hidden 'Hidden) where
    serialize (SomeDep2'' (LL size1 size2)) = serialize size1 ++ serialize size2
    deserialize bs =
        case deserialize bs of
            (Some1 SNat size1, bs') ->
                case deserialize bs' of
                    (Some1 SNat size2, bs'') ->
                        (SomeDep2'' (LL size1 size2), bs'')


instance Dep2Deserialize RR where
    type ActualDepLevel1 RR = 'Requiring
    type ActualDepLevel2 RR = 'Requiring
    dep2Deserialize ((KnwlgK (SNat :: Sing x)) `SomeDepStatesCons` (KnwlgK (SNat :: Sing y)) `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize @(Vector Word8 x) bs of
            (arr1, bs') ->
                case deserialize @(Vector Word8 y) bs' of
                    (arr2, bs'') ->
                        (SomeDep2 (KnowledgeK SNat) (KnowledgeK SNat) (RR arr1 arr2), bs'')

instance Dep2Deserialize RN where
    type ActualDepLevel1 RN = 'Requiring
    type ActualDepLevel2 RN = 'NonDep
    dep2Deserialize ((KnwlgK (SNat :: Sing x)) `SomeDepStatesCons` y `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize @(Vector Word8 x) bs of
            (arr1, bs') ->
                withKnwlg y $ \y' -> (SomeDep2 (KnowledgeK SNat) y' (RN arr1), bs')

instance Dep2Deserialize RL where
    type ActualDepLevel1 RL = 'Requiring
    type ActualDepLevel2 RL = 'Learning
    dep2Deserialize ((KnwlgK (SNat :: Sing x)) `SomeDepStatesCons` y `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize @(Vector Word8 x) bs of
            (arr1, bs') ->
                case deserialize @(Some1 (Sing :: Nat -> Type)) bs' of
                    (Some1 y' size2, bs'') ->
                        withKnwlg y $ \y'' -> case sameKnowlege y'' (KnowledgeK y') of
                            Nothing -> error $ "Already knew type index was equal to " ++ show y'' ++ ", but now learned that it is equal to " ++ show y'
                            Just Refl ->
                                (SomeDep2 (KnowledgeK SNat) (KnowledgeK y') (RL arr1 size2), bs'')

instance Dep2Deserialize NR where
    type ActualDepLevel1 NR = 'NonDep
    type ActualDepLevel2 NR = 'Requiring
    dep2Deserialize (k1 `SomeDepStatesCons` (KnwlgK (SNat :: Sing y)) `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize @(Vector Word8 y) bs of
            (arr2, bs') ->
                withKnwlg k1 $ \k1' -> (SomeDep2 k1' (KnowledgeK SNat) (NR arr2), bs')

instance Dep2Deserialize NN where
    type ActualDepLevel1 NN = 'NonDep
    type ActualDepLevel2 NN = 'NonDep
    dep2Deserialize (k1 `SomeDepStatesCons` k2 `SomeDepStatesCons` SomeDepStatesNil) bs =
        withKnwlg k1 $ \k1' -> withKnwlg k2 $ \k2' -> (SomeDep2 k1' k2' NN, bs)

instance Dep2Deserialize NL where
    type ActualDepLevel1 NL = 'NonDep
    type ActualDepLevel2 NL = 'Learning
    dep2Deserialize (k1 `SomeDepStatesCons` _ `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize bs of
            (Some1 SNat size2, bs') ->
                withKnwlg k1 $ \k1' -> (SomeDep2 k1' (KnowledgeK SNat) (NL size2), bs')

instance Dep2Deserialize LR where
    type ActualDepLevel1 LR = 'Learning
    type ActualDepLevel2 LR = 'Requiring
    dep2Deserialize (_ `SomeDepStatesCons` (KnwlgK (SNat :: Sing y)) `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize bs of
            (Some1 SNat size1, bs') ->
                case deserialize @(Vector Word8 y) bs of
                    (arr2, bs'') ->
                        (SomeDep2 (KnowledgeK SNat) (KnowledgeK SNat) (LR size1 arr2), bs'')

instance Dep2Deserialize LN where
    type ActualDepLevel1 LN = 'Learning
    type ActualDepLevel2 LN = 'NonDep
    dep2Deserialize (_ `SomeDepStatesCons` k2 `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize bs of
            (Some1 SNat size1, bs') ->
                withKnwlg k2 $ \k2' -> (SomeDep2 (KnowledgeK SNat) k2' (LN size1), bs')

instance Dep2Deserialize LL where
    type ActualDepLevel1 LL = 'Learning
    type ActualDepLevel2 LL = 'Learning
    dep2Deserialize (_ `SomeDepStatesCons` _ `SomeDepStatesCons` SomeDepStatesNil) bs =
        case deserialize bs of
            (Some1 SNat size1, bs') ->
                case deserialize bs' of
                    (Some1 SNat size2, bs'') ->
                        (SomeDep2 (KnowledgeK SNat) (KnowledgeK SNat) (LL size1 size2), bs'')

testRRRR = dep2Deserialize @Nat @Nat @(Prod2 RR RR) (KnwlgK (SNat @1) `SomeDepStatesCons` KnwlgK (SNat @2) `SomeDepStatesCons` SomeDepStatesNil) [0..5]
testRLRRU = dep2Deserialize @Nat @Nat @(Prod2 RL RR) (KnwlgK (SNat @1) `SomeDepStatesCons` KnwlgU `SomeDepStatesCons` SomeDepStatesNil) [0,1,2,3]
testRLRRKGood = dep2Deserialize @Nat @Nat @(Prod2 RL RR) (KnwlgK (SNat @1) `SomeDepStatesCons` KnwlgK (SNat @1) `SomeDepStatesCons` SomeDepStatesNil) [0,1,2,3]
testRLRRKBad = dep2Deserialize @Nat @Nat @(Prod2 RL RR) (KnwlgK (SNat @1) `SomeDepStatesCons` KnwlgK (SNat @2) `SomeDepStatesCons` SomeDepStatesNil) [0,1,2,3]

data WrapNL size1 size2 = WrapNL
    { nl :: NL size1 size2
    } deriving (GHC.Generic, Show)
      deriving Dep2Deserialize via Var2Wrapper WrapNL
instance GenericK WrapNL (size1 :&&: size2 :&&: LoT0) where
    type RepK WrapNL = Field (NL :$: Var0 :@: Var1)
testDeserializeSomeDep2 :: (SomeDep2 WrapNL 'Unknown 'Known, [Word8])
testDeserializeSomeDep2 = deserializeSomeDep2 [0, 1, 2, 3]

data L1L2R1R2 size1 size2 = L1L2R1R2
    { size1 :: LN size1 size2
    , size2 :: NL size1 size2
    , arr1  :: RN size1 size2
    , arr2  :: NR size1 size2
    } deriving (GHC.Generic, Show)
      deriving Dep2Deserialize via Var2Wrapper L1L2R1R2
instance GenericK L1L2R1R2 (size1 :&&: size2 :&&: LoT0) where
    type RepK L1L2R1R2 =
            (   Field (LN :$: Var0 :@: Var1)
            :*: 
                Field (NL :$: Var0 :@: Var1)
            )
        :*:
            (   Field (RN :$: Var0 :@: Var1)
            :*:
                Field (NR :$: Var0 :@: Var1)
            )
testDeserializeSomeDep2L1L2R1R2 :: (SomeDep2 L1L2R1R2 'Known 'Known, [Word8])
testDeserializeSomeDep2L1L2R1R2 = deserializeSomeDep2 [0, 1, 2, 3]

data SingSize1 (size1 :: Nat) (size2 :: Nat) = Sing2
    { size1 :: Sing size1
    } deriving (GHC.Generic, Show)
      deriving Dep2Deserialize via Var2Wrapper SingSize1
instance GenericK SingSize1 (size1 :&&: size2 :&&: LoT0) where
    type RepK SingSize1 = Field (Sing :$: Var0)
testDeserializeSomeDep2SingSize1 :: (SomeDep2 SingSize1 'Known 'Unknown, [Word8])
testDeserializeSomeDep2SingSize1 = deserializeSomeDep2 [0, 1, 2, 3]


--instance Dep2Deserialize RR where
--    type DepLevel1 RR = 'Requiring
--    type DepLevel2 RR = 'Requiring
--    dep2deserialize :: forall x y. (SingI x, SingI y) => [Word8] -> (SomeDep2'' ('Exposed x) ('Exposed y) RR, [Word8])
--    dep2deserialize = deserialize
--instance Dep2Deserialize NN where
--    type DepLevel1 NN = 'NonDep
--    type DepLevel2 NN = 'NonDep
--    dep2deserialize :: forall x y. ((), ()) => [Word8] -> (SomeDep2'' ('Exposed x) ('Exposed y) NN, [Word8])
--    dep2deserialize = deserialize
--instance Dep2Deserialize LL where
--    type DepLevel1 LL = 'Learning
--    type DepLevel2 LL = 'Learning
--    dep2deserialize :: forall x y. ((), ()) => [Word8] -> (SomeDep2'' 'Hidden 'Hidden LL, [Word8])
--    dep2deserialize = deserialize
--
data TwoVar (size1 :: Nat) (size2 :: Nat) = TwoVar
    { size1 :: LN size1 size2
    , size2 :: NL size1 size2
    , arr1  :: RN size1 size2
    , arr2  :: NR size1 size2
    } deriving (Show, GHC.Generic)

--instance Serialize (SomeDep2'' 'Hidden 'Hidden TwoVar) where
--    --serialize (SomeDep2'' (TwoVar size1 size2 arr1 arr2)) = serialize (SomeDep2'' size1) ++ serialize (SomeDep2'' size2) ++ serialize (SomeDep2'' arr1) ++ serialize (SomeDep2'' arr2)
--    deserialize bs =
--        case deserialize bs of
--            (SomeDep2'' (LN SNat :: LN x _) :: SomeDep2'' 'Hidden ('Exposed _) LN, bs') ->
--                let size1 = LN SNat in
--                case deserialize bs' of
--                    (SomeDep2'' (NL SNat :: NL _ y) :: SomeDep2'' ('Exposed _) 'Hidden NL, bs'') ->
--                        let size2 = NL SNat in
--                        case deserialize bs'' of
--                            (SomeDep2'' arr1 :: SomeDep2'' ('Exposed x) ('Exposed y) RN, bs''') ->
--                                case deserialize bs''' of
--                                    (SomeDep2'' arr2 :: SomeDep2'' ('Exposed x) ('Exposed y) NR, bs'''') ->
--                                        (SomeDep2'' (TwoVar size1 size2 arr1 arr2), bs'''')

--sd2uu = SomeDep2 @'Unknown @'Unknown $ TwoVar SNat SNat (0 :> Nil) Nil
--sd2kk = SomeDep2 @'Known @'Known $ TwoVar SNat SNat (0 :> Nil) Nil
--_ = case sd2kk of SomeDep2 (_ :: TwoVar a b) -> SomeSing (sing @a)
----_ = case sd2uu of SomeDep2 (_ :: TwoVar a b) -> SomeSing (sing @a)

{-
instance Reifies v1 (Sing (y :: Nat)) => Serialize (SomeDep2 NR 'Unknown 'Known) where
    serialize (SomeDep2 (NR arr2)) = serialize arr2
    deserialize bs =
        withSingI (reflect @v1 Proxy) $
        case deserialize @(Vector Word8 y) bs of
            (arr2, bs') ->
                (SomeDep2 (NR arr2), bs')

instance Serialize (SomeDep2 NN 'Unknown 'Unknown) where
    serialize (SomeDep2 NN) = []
    deserialize bs =
        (SomeDep2 NN, bs)

instance Serialize (SomeDep2 NL 'Unknown 'Known) where
    serialize (SomeDep2 (NL size2)) = serialize size2
    deserialize bs =
        case deserialize bs of
            (Some1 SNat size2, bs') ->
                (SomeDep2 (NL size2), bs')

instance Reifies v1 (Sing (y :: Nat)) => Serialize (SomeDep2 LR 'Known 'Known) where
    serialize (SomeDep2 (LR size1 arr2)) = serialize size1 ++ serialize arr2
    deserialize bs =
        withSingI (reflect @v1 Proxy) $
        case deserialize bs of
            (Some1 SNat size1, bs') ->
                case deserialize @(Vector Word8 y) bs' of
                    (arr2, bs'') ->
                        (SomeDep2 (LR size1 arr2), bs'')

instance Serialize (SomeDep2 LN 'Known 'Unknown) where
    serialize (SomeDep2 (LN size1)) = serialize size1
    deserialize bs =
        case deserialize bs of
            (Some1 SNat size1, bs') ->
                (SomeDep2 (LN size1), bs')
-}

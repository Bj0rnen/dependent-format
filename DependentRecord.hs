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

module DependentRecord where

import Data.Singletons
import Data.Singletons.TH
import GHC.TypeNats
import Data.Singletons.TypeLits
import Data.Kind

import qualified GHC.Generics as GHC hiding (from, to)
import Generics.SOP hiding (Sing, Nil, SingI, sing)
import qualified Generics.SOP as SOP
import Generics.SOP.Classes (Same)
import GHC.TypeLits (TypeError(..), ErrorMessage(..))
import           Generics.Kind hiding (Nat, (:~:))
import qualified Generics.Kind as K

import Data.Proxy
import Data.Constraint
import Unsafe.Coerce
import GHC.Types (Any)
import Data.Coerce
import Data.Functor.Const

import Data.Word
import Data.Bits
import Numeric.Natural
import Data.Kind.Fin (ltNat, predecessor, subNat)
import Data.Singletons.Fin

import Exinst
import Data.Reflection

data Vector :: Type -> Nat -> Type where
    Nil :: Vector a 0
    (:>) :: IsNonZero (1 + n) ~ 'True => a -> Vector a n -> Vector a (1 + n)  -- NOTE: The IsNonZero thing makes ifZeroElse's 0-case fail this pattern match. Hope there's some nicer way to achieve this.
deriving instance Show a => Show (Vector a n)
infixr :>

data DependentPair (size :: Nat) = DependentPair
    { size :: Sing size
    , arr :: Vector Word8 size
    } deriving (Show, GHC.Generic1)

lol :: GHC.Rep1 DependentPair 2
lol = GHC.from1 (DependentPair SNat (1 :> 2 :> Nil))

class Serialize a where
    serialize :: a -> [Word8]
    deserialize :: [Word8] -> (a, [Word8])

newtype Generic1Wrapper f a = Generic1Wrapper { unwrapGeneric1 :: f a }
instance (GHC.Generic1 f, Serialize (GHC.Rep1 f x), HasDepLevel f) => Serialize (Generic1Wrapper f x) where
    serialize (Generic1Wrapper a) = serialize $ GHC.from1 a
    deserialize bs =
        case deserialize bs of
            (a, bs') ->
                (Generic1Wrapper (GHC.to1 a), bs')


instance Serialize Word8 where
    serialize a = [a]
    deserialize (b : bs) = (b, bs)

--instance KnownNat n => Serialize (Sing (n :: Nat)) where  -- 8-bit
--    serialize SNat = [fromIntegral $ natVal @n Proxy]
--    deserialize (n : bs) =
--        if fromIntegral n == natVal @n Proxy then
--            (SNat, bs)
--        else
--            error "Deserialized wrong SNat"
instance SingI n => Serialize (Sing (n :: Nat)) where  -- 8-bit
    serialize SNat = serialize $ natVal @n Proxy
    deserialize bs =
        withKnownNat @n sing $
            case deserialize bs of
                (n :: Natural, bs') ->
                    if n == natVal @n Proxy then
                        (SNat , bs')
                    else
                        error "Deserialized wrong SNat"
--instance Serialize (SomeSing Nat) where
--    serialize (SomeSing (SNat :: Sing n)) = serialize (SNat @n)
--    deserialize bs =
--        case deserialize bs of
--            (a :: Word8, bs') ->
--                case someNatVal (fromIntegral a) of
--                    SomeNat (Proxy :: Proxy n) ->
--                        (SomeSing @Nat @n SNat, bs')
instance Serialize Natural where  -- 8-bit
    serialize n = [fromIntegral n]
    deserialize bs =
        case deserialize bs of
            (a :: Word8, bs') ->
                (fromIntegral a, bs')

newtype Magic n = Magic (KnownNat n => Dict (KnownNat n))
magic :: forall n m o. (Natural -> Natural -> Natural) -> (KnownNat n, KnownNat m) :- KnownNat o
magic f = Sub $ unsafeCoerce (Magic Dict) (natVal (Proxy :: Proxy n) `f` natVal (Proxy :: Proxy m))
axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))
plusMinusInverse :: forall n m. (n `CmpNat` (1 + m) ~ 'LT) :- ((n + (m - n)) ~ m)
plusMinusInverse = Sub axiom
unsafeSubNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n - m)
unsafeSubNat = magic (-)
type family
    IsNonZero (n :: Nat) = (nonzero :: Bool) where
    IsNonZero 0 = 'False
    IsNonZero n = 'True
ifZeroElse :: forall n r. KnownNat n => (n ~ 0 => r) -> (forall n1. (KnownNat n1, n ~ (1 + n1), IsNonZero n ~ 'True) => Proxy n1 -> r) -> r
ifZeroElse z s =
    case sameNat @n @0 Proxy Proxy of
        Just Refl -> z
        Nothing ->
            withDict (axiom :: Dict (1 `CmpNat` (1 + n) ~ 'LT)) $
                withDict (axiom :: Dict (IsNonZero n ~ 'True)) (s Proxy) \\ unsafeSubNat @n @1 \\ plusMinusInverse @1 @n
samePredecessor :: forall n n1 n2. (n ~ (1 + n1), n ~ (1 + n2)) :- (n1 ~ n2)
samePredecessor = Sub axiom
addNonZero :: forall n m. (IsNonZero n ~ 'True) :- (CmpNat m (m + n) ~ 'LT)
addNonZero = Sub axiom

instance (Serialize a, SingI n) => Serialize (Vector a n) where
    serialize (v :: Vector a n) =
        withKnownNat @n sing $
            ifZeroElse @n [] $ \_ ->
                case v of
                    x :> xs ->
                        serialize x ++ serialize xs \\ samePredecessor @n
    deserialize bs =
        withKnownNat @n sing $
            ifZeroElse @n (Nil, bs) $ \(Proxy :: Proxy n1) ->
                case deserialize @a bs of
                    (a, bs') ->
                        case deserialize @(Vector a n1) bs' of
                            (as, bs'') -> (a :> as, bs'')

instance Serialize (f p) => Serialize (GHC.Rec1 f p) where
    serialize (GHC.Rec1 a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (GHC.Rec1 a, bs')

instance Serialize (f p) => Serialize (GHC.M1 i c f p) where
    serialize (GHC.M1 a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (GHC.M1 a, bs')

instance (Serialize (a p), Serialize (b p)) => Serialize ((a GHC.:*: b) p) where
    serialize (a GHC.:*: b) = serialize a ++ serialize b
    deserialize bs =
        case deserialize @(a p) bs of
            (a, bs') ->
                case deserialize @(b p) bs' of
                    (b, bs'') -> (a GHC.:*: b, bs'')

instance Serialize a => Serialize (GHC.K1 i a p) where
    serialize (GHC.K1 a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (GHC.K1 a, bs')

instance Serialize (GHC.U1 p) where
    serialize GHC.U1 = []
    deserialize bs = (GHC.U1, bs)

slol = serialize lol
dlol :: (GHC.Rep1 DependentPair 2, [Word8])
dlol = deserialize [2, 1, 2]

lol' :: DependentPair 2
lol' = GHC.to1 (fst dlol)

instance Serialize (Some1 DependentPair) where
    serialize (Some1 SNat (DependentPair SNat arr)) = serialize arr
    deserialize bs =
        case deserialize bs of
            (FromSing (SNat :: Sing (size :: Nat)), bs') ->
                case deserialize bs' of
                    (arr :: Vector Word8 size, bs'') ->
                        (Some1 SNat (DependentPair SNat arr), bs'')

instance Serialize (Some1 f) => Serialize (Some1 (GHC.M1 i c f)) where
    serialize (Some1 (s :: Sing a) (GHC.M1 a)) = serialize (Some1 s a)
    deserialize bs =
        case deserialize bs of
            (Some1 s a, bs') -> (Some1 s (GHC.M1 a), bs')
instance Serialize (Some1 f) => Serialize (Some1 (GHC.Rec1 f)) where
    serialize (Some1 s (GHC.Rec1 a)) = serialize (Some1 s a)
    deserialize bs =
        case deserialize bs of
            (Some1 s a, bs') -> (Some1 s (GHC.Rec1 a), bs')
--instance Serialize (Some1 (GHC.K1 i a)) where
--    serialize (Some1 s (GHC.K1 a)) = serialize a
--    deserialize bs =
--        case deserialize bs of
--            (a, bs') -> (Some1 ? (GHC.K1 a), bs')

instance (SingKind t, Serialize (Demote t)) => Serialize (Some1 (Sing :: t -> Type)) where
    serialize (Some1 s1 s2) = serialize (FromSing s2)
    deserialize bs =
        case deserialize bs of
            (FromSing s, bs') -> (Some1 s s, bs')

serializeSome1 :: (GHC.Generic1 f, Serialize (Some1 (GHC.Rep1 f))) => Some1 f -> [Word8]
serializeSome1 (Some1 s a) = serialize (Some1 s (GHC.from1 a))
deserializeSome1 :: (GHC.Generic1 f, Serialize (Some1 (GHC.Rep1 f))) => [Word8] -> (Some1 f, [Word8])
deserializeSome1 bs =
    case deserialize bs of
        (Some1 (s :: Sing a) a, bs') ->
            (Some1 s (GHC.to1 a), bs')

someLol :: Some1 (GHC.Rep1 DependentPair)
someLol = Some1 SNat $ GHC.from1 (DependentPair SNat (1 :> 2 :> Nil))
sdp = serialize someLol

instance Serialize Word16 where
    serialize a = [fromIntegral (a .&. 0xFF00) `shiftR` 8, fromIntegral (a .&. 0xFF)]
    deserialize bs =
        case deserialize bs of
            (a :> b :> Nil :: Vector Word8 2, bs') -> ((fromIntegral a) `shiftL` 8 .|. fromIntegral b, bs')

data UseSizeManyTimes (size :: Nat) = UseSizeManyTimes
    { whatever :: Word8
    , size :: Sing size
    , arr1 :: Vector Word8 size
    , sizeAgain :: Sing size
    , whatever2 :: Word8
    , arr2 :: Vector Word16 size
    , arr3 :: Vector Word8 size
    , sizeAgainAgain :: Sing size
    } deriving (GHC.Generic1, Show)

someUST :: Some1 UseSizeManyTimes
someUST = Some1 SNat $ UseSizeManyTimes 123 SNat (1 :> 2 :> 3 :> Nil) SNat 42 (4 :> 5 :> 6 :> Nil) (7 :> 8 :> 9:> Nil) SNat
sust = serializeSome1 someUST

dust :: Some1 UseSizeManyTimes
dust = fst $ deserializeSome1 [123,3,1,2,3,3,42,0,4,0,5,0,6,7,8,9,3]

dust2 :: Some1 UseSizeManyTimes
dust2 = fst $ deserializeSome1 [0,0,0,0,0]

data NeverUseSize (size :: Nat) = NeverUseSize
    { x :: Word8
    , y :: Word8
    } deriving (GHC.Generic1, Show, HasDepLevel)
      deriving Serialize via (Generic1Wrapper NeverUseSize size)

dnus :: NeverUseSize a
dnus = fst $ deserialize [1, 2]
snus :: [Word8]
snus = serialize dnus

-- Requiring: (forall x. SingI x => Serialize (f x))
--     A field that's only (de)serializable when the type index is known.
--
-- NonDep:    (forall x. Serialize (f x), forall x y. Coercible (f x) (f y))
--     A field that's always (de)serializable, independently if type index.
--
-- Learning:  (Serialize (Some1 f))
--     A field that can (de)serialize without knowing the type index.
--     Deserializing recovers the type index.
data DepLevel = Requiring | NonDep | Learning
data DepState = Unknown | Known
type family
    ApplyDepLevel (f :: DepLevel) (a :: DepState) :: DepState where
    ApplyDepLevel 'Requiring 'Unknown = Error "Required type index not known"
    ApplyDepLevel 'Requiring 'Known = 'Known
    ApplyDepLevel 'NonDep a = a
    ApplyDepLevel 'Learning _ = 'Known
data Knowledge :: DepState -> a -> Type where
    KnowledgeU :: Knowledge 'Unknown a
    KnowledgeK :: Sing a -> Knowledge 'Known a
data Knwlg :: DepState -> Type -> Type where
    KnwlgU :: Knwlg 'Unknown a
    KnwlgK :: forall (x :: a). Sing x -> Knwlg 'Known a
deriving instance Show (Sing a) => Show (Knowledge d a)
data SomeDep1 :: DepState -> (a -> Type) -> Type where
    SomeDep1 :: forall d f x. Knowledge d x -> f x -> SomeDep1 d f
deriving instance (forall x. (Show (f x), Show (Sing x))) => Show (SomeDep1 d f)
data SomeDep2 :: (a -> b -> Type) -> DepState -> DepState -> Type where
    SomeDep2 :: forall d1 d2 f x y. Knowledge d1 x -> Knowledge d2 y -> f x y -> SomeDep2 f d1 d2
deriving instance (forall x y. (Show (f x y), Show (Sing x), Show (Sing y))) => Show (SomeDep2 f d1 d2)

data SomeDepStates :: [(Type, DepState)] -> Type where
    SomeDepStatesNil :: SomeDepStates '[]
    SomeDepStatesCons :: Knwlg w a -> SomeDepStates xs -> SomeDepStates ('(a, w) ': xs)
infixr `SomeDepStatesCons`

withKnwlg :: forall d a r. Knwlg d a -> (forall (x :: a). Knowledge d x -> r) -> r
withKnwlg KnwlgU f = f KnowledgeU
withKnwlg (KnwlgK s) f = f (KnowledgeK s)

knowledgeToKnwlg :: forall d (x :: a). Knowledge d x -> Knwlg d a
knowledgeToKnwlg KnowledgeU = KnwlgU
knowledgeToKnwlg (KnowledgeK s) = KnwlgK s

someDep2ToSomeDepState2 :: forall d1 d2 a b f. SomeDep2 (f :: a -> b -> Type) d1 d2 -> SomeDepStates '[ '(a, d1), '(b, d2)]
someDep2ToSomeDepState2 (SomeDep2 KnowledgeU KnowledgeU _) = KnwlgU `SomeDepStatesCons` KnwlgU `SomeDepStatesCons` SomeDepStatesNil
someDep2ToSomeDepState2 (SomeDep2 KnowledgeU (KnowledgeK y) a) = KnwlgU `SomeDepStatesCons` (KnwlgK y) `SomeDepStatesCons` SomeDepStatesNil
someDep2ToSomeDepState2 (SomeDep2 (KnowledgeK x) KnowledgeU a) = (KnwlgK x) `SomeDepStatesCons` KnwlgU `SomeDepStatesCons` SomeDepStatesNil
someDep2ToSomeDepState2 (SomeDep2 (KnowledgeK x) (KnowledgeK y) a) = (KnwlgK x) `SomeDepStatesCons` (KnwlgK y) `SomeDepStatesCons` SomeDepStatesNil

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


deserializeSomeDep2 :: forall a b (f :: a -> b -> Type) d1 d2.
    ( Dep2Deserialize f
    , d1 ~ DepLevel1 f 'Unknown
    , d2 ~ DepLevel2 f 'Unknown
    , Ctx1 f 'Unknown
    , Ctx2 f 'Unknown
    ) => [Word8] -> (SomeDep2 f (DepLevel1 f 'Unknown) (DepLevel2 f 'Unknown), [Word8])
deserializeSomeDep2 = dep2Deserialize (KnwlgU `SomeDepStatesCons` KnwlgU `SomeDepStatesCons` SomeDepStatesNil)


data Prod2 (l :: a -> b -> Type) (r :: a -> b -> Type) x y = Prod2 (l x y) (r x y)
    deriving Show

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

testRRRR = dep2Deserialize @Nat @Nat @(Prod2 RR RR) (KnwlgK (SNat @1) `SomeDepStatesCons` KnwlgK (SNat @2) `SomeDepStatesCons` SomeDepStatesNil) [0..5]
testRLRRU = dep2Deserialize @Nat @Nat @(Prod2 RL RR) (KnwlgK (SNat @1) `SomeDepStatesCons` KnwlgU `SomeDepStatesCons` SomeDepStatesNil) [0,1,2,3]
testRLRRKGood = dep2Deserialize @Nat @Nat @(Prod2 RL RR) (KnwlgK (SNat @1) `SomeDepStatesCons` KnwlgK (SNat @1) `SomeDepStatesCons` SomeDepStatesNil) [0,1,2,3]
testRLRRKBad = dep2Deserialize @Nat @Nat @(Prod2 RL RR) (KnwlgK (SNat @1) `SomeDepStatesCons` KnwlgK (SNat @2) `SomeDepStatesCons` SomeDepStatesNil) [0,1,2,3]

newtype Var2Wrapper f a b = Var2Wrapper { unwrapVar2 :: f a b }
instance (forall x y. K.GenericK f (x K.:&&: y K.:&&: K.LoT0), Dep2Deserialize (Curry2 (K.RepK f))) => Dep2Deserialize (Var2Wrapper f) where
    type DepLevel1 (Var2Wrapper f) d = DepLevel1 (Curry2 (K.RepK f)) d
    type DepLevel2 (Var2Wrapper f) d = DepLevel2 (Curry2 (K.RepK f)) d
    type Ctx1 (Var2Wrapper f) (d :: DepState) = (Ctx1 (Curry2 (K.RepK f)) d)
    type Ctx2 (Var2Wrapper f) (d :: DepState) = (Ctx2 (Curry2 (K.RepK f)) d)
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Var2Wrapper f) = ActualDepLevel1 (Curry2 (K.RepK f))
    type ActualDepLevel2 (Var2Wrapper f) = ActualDepLevel2 (Curry2 (K.RepK f))
    dep2Deserialize depStates bs =
        case dep2Deserialize depStates bs of
            (SomeDep2 k1 k2 (Curry2 a :: Curry2 (K.RepK f) x y), bs') -> (SomeDep2 k1 k2 (Var2Wrapper (K.toK a) :: Var2Wrapper f x y), bs')

instance Dep2Deserialize f => Dep2Deserialize (Curry2 (K.Field (f K.:$: K.Var0 'K.:@: K.Var1))) where
    type DepLevel1 (Curry2 (K.Field (f K.:$: K.Var0 'K.:@: K.Var1))) d = DepLevel1 f d
    type DepLevel2 (Curry2 (K.Field (f K.:$: K.Var0 'K.:@: K.Var1))) d = DepLevel2 f d
    type Ctx1 (Curry2 (K.Field (f K.:$: K.Var0 'K.:@: K.Var1))) (d :: DepState) = (Ctx1 f d)
    type Ctx2 (Curry2 (K.Field (f K.:$: K.Var0 'K.:@: K.Var1))) (d :: DepState) = (Ctx2 f d)
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Curry2 (K.Field (f K.:$: K.Var0 'K.:@: K.Var1))) = ActualDepLevel1 f
    type ActualDepLevel2 (Curry2 (K.Field (f K.:$: K.Var0 'K.:@: K.Var1))) = ActualDepLevel2 f
    dep2Deserialize depStates bs =
        case dep2Deserialize depStates bs of
            (SomeDep2 k1 k2 (a :: f x y), bs') -> (SomeDep2 k1 k2 (Curry2 (K.Field a)), bs')

instance
    ( SDecide a
    , SDecide b
    , (Dep2Deserialize (Curry2 l))
    , (Dep2Deserialize (Curry2 r))
    ) => Dep2Deserialize (Curry2 ((l :: K.LoT (a -> b -> Type) -> Type) K.:*: (r :: K.LoT (a -> b -> Type) -> Type))) where
    type DepLevel1 (Curry2 (l K.:*: r)) d = DepLevel1 (Prod2 (Curry2 l) (Curry2 r)) d
    type DepLevel2 (Curry2 (l K.:*: r)) d = DepLevel2 (Prod2 (Curry2 l) (Curry2 r)) d
    type Ctx1 (Curry2 (l K.:*: r)) (d :: DepState) = (Ctx1 (Prod2 (Curry2 l) (Curry2 r)) d)
    type Ctx2 (Curry2 (l K.:*: r)) (d :: DepState) = (Ctx2 (Prod2 (Curry2 l) (Curry2 r)) d)
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Curry2 (l K.:*: r)) = ActualDepLevel1 (Prod2 (Curry2 l) (Curry2 r))
    type ActualDepLevel2 (Curry2 (l K.:*: r)) = ActualDepLevel2 (Prod2 (Curry2 l) (Curry2 r))
    dep2Deserialize depStates bs =
        case dep2Deserialize depStates bs of
            (SomeDep2 k1 k2 (Prod2 (Curry2 x) (Curry2 y) :: (Prod2 (Curry2 l) (Curry2 r)) x y), bs') -> (SomeDep2 k1 k2 (Curry2 (x K.:*: y)), bs')

data WrapNL size1 size2 = WrapNL
    { nl :: NL size1 size2
    } deriving (GHC.Generic, Show)
      deriving Dep2Deserialize via Var2Wrapper WrapNL
instance K.GenericK WrapNL (size1 K.:&&: size2 K.:&&: K.LoT0) where
    type RepK WrapNL = K.Field (NL K.:$: K.Var0 K.:@: K.Var1)
testDeserializeSomeDep2 :: (SomeDep2 WrapNL 'Unknown 'Known, [Word8])
testDeserializeSomeDep2 = deserializeSomeDep2 [0, 1, 2, 3]

data L1L2R1R2 size1 size2 = L1L2R1R2
    { size1 :: LN size1 size2
    , size2 :: NL size1 size2
    , arr1  :: RN size1 size2
    , arr2  :: NR size1 size2
    } deriving (GHC.Generic, Show)
      deriving Dep2Deserialize via Var2Wrapper L1L2R1R2
instance K.GenericK L1L2R1R2 (size1 K.:&&: size2 K.:&&: K.LoT0) where
    type RepK L1L2R1R2 =
            (   K.Field (LN K.:$: K.Var0 K.:@: K.Var1)
            K.:*: 
                K.Field (NL K.:$: K.Var0 K.:@: K.Var1)
            )
        K.:*:
            (   K.Field (RN K.:$: K.Var0 K.:@: K.Var1)
            K.:*:
                K.Field (NR K.:$: K.Var0 K.:@: K.Var1)
            )
testDeserializeSomeDep2L1L2R1R2 :: (SomeDep2 L1L2R1R2 'Known 'Known, [Word8])
testDeserializeSomeDep2L1L2R1R2 = deserializeSomeDep2 [0, 1, 2, 3]


-- TODO: Above is very hard-coded. Thinking we should have something like the below
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
instance Dep2Deserialize (Select1of2 t :: a -> b -> Type) => Dep2Deserialize (Curry2 (K.Field ((t :: a -> Type) K.:$: K.Var0 :: K.Atom (a -> b -> Type) Type))) where
    type DepLevel1 (Curry2 (K.Field ((t :: a -> Type) K.:$: K.Var0 :: K.Atom (a -> b -> Type) Type))) d = DepLevel1 (Select1of2 t :: a -> b -> Type) d
    type DepLevel2 (Curry2 (K.Field ((t :: a -> Type) K.:$: K.Var0 :: K.Atom (a -> b -> Type) Type))) d = DepLevel2 (Select1of2 t :: a -> b -> Type) d
    type Ctx1 (Curry2 (K.Field ((t :: a -> Type) K.:$: K.Var0 :: K.Atom (a -> b -> Type) Type))) (d :: DepState) = Ctx1 (Select1of2 t :: a -> b -> Type) d
    type Ctx2 (Curry2 (K.Field ((t :: a -> Type) K.:$: K.Var0 :: K.Atom (a -> b -> Type) Type))) (d :: DepState) = Ctx2 (Select1of2 t :: a -> b -> Type) d
    -- TODO: Would be nice if this was all that we needed, so that we could drop DepLevel and Ctx entirely
    type ActualDepLevel1 (Curry2 (K.Field ((t :: a -> Type) K.:$: K.Var0 :: K.Atom (a -> b -> Type) Type))) = ActualDepLevel1 (Select1of2 t :: a -> b -> Type)
    type ActualDepLevel2 (Curry2 (K.Field ((t :: a -> Type) K.:$: K.Var0 :: K.Atom (a -> b -> Type) Type))) = ActualDepLevel2 (Select1of2 t :: a -> b -> Type)
    dep2Deserialize depStates bs =
        case dep2Deserialize depStates bs of
            (SomeDep2 k1 k2 (Select1of2 a), bs') ->
                (SomeDep2 k1 k2 (Curry2 (K.Field a)), bs')

data SingSize1 (size1 :: Nat) (size2 :: Nat) = Sing2
    { size1 :: Sing size1
    } deriving (GHC.Generic, Show)
      deriving Dep2Deserialize via Var2Wrapper SingSize1
instance K.GenericK SingSize1 (size1 K.:&&: size2 K.:&&: K.LoT0) where
    type RepK SingSize1 = K.Field (Sing K.:$: K.Var0)
testDeserializeSomeDep2SingSize1 :: (SomeDep2 SingSize1 'Known 'Unknown, [Word8])
testDeserializeSomeDep2SingSize1 = deserializeSomeDep2 [0, 1, 2, 3]














-- Already defined elsewhere.
--data Knowledge :: DepState -> a -> Type where
--    KnowledgeU :: Knowledge 'Unknown x
--    KnowledgeK :: Sing (x :: a) -> Knowledge 'Known x
data PartialKnowledge (ks :: Type) (ds :: [DepState]) where
    PartialKnowledgeNil  :: PartialKnowledge Type '[]
    PartialKnowledgeCons :: Knowledge d (x :: a) -> PartialKnowledge ks ds -> PartialKnowledge (a -> ks) (d ': ds)
data PartiallyKnown (ks :: Type) (f :: ks) (ds :: [DepState]) where
    PartiallyKnownNil  :: f -> PartiallyKnown Type f '[]
    PartiallyKnownCons :: Knowledge d (x :: a) -> PartiallyKnown ks (f x) ds -> PartiallyKnown (a -> ks) f (d ': ds)
--instance Show f => Show (PartiallyKnown Type f ds)
--instance (forall x. Show (PartiallyKnown ks (f x) ds), forall (x :: a). Show (Sing x)) => Show (PartiallyKnown (a -> ks) f ds)


class DepKDeserialize (f :: ks) where
    --type TaughtBy (f :: ks) (ds :: [DepState]) :: [DepState]
    --depKDeserialize :: PartialKnowledge ks ds -> [Word8] -> (PartiallyKnown ks f (TaughtBy f ds), [Word8])
--instance (SingKind a, Serialize (Demote a)) => DepKDeserialize (Sing :: a -> Type) where
--    type TaughtBy Sing '[ _] = '[ 'Known]
--    depKDeserialize (PartialKnowledgeCons _ PartialKnowledgeNil) bs =
--        case deserialize bs of
--            (FromSing s, bs') ->
--                (PartiallyKnownCons (KnowledgeK s) (PartiallyKnownNil s), bs')
--instance Serialize t => DepKDeserialize (Vector t) where
--    type TaughtBy (Vector t) '[ 'Known] = '[ 'Known]
--    depKDeserialize (PartialKnowledgeCons (KnowledgeK (SNat :: Sing x)) PartialKnowledgeNil) bs =
--        case deserialize @(Vector t x) bs of
--            (a, bs') ->
--                (PartiallyKnownCons (KnowledgeK (SNat :: Sing x)) (PartiallyKnownNil a), bs')
--
----sameKnowlege :: forall (d1 :: DepState) (d2 :: DepState) (x1 :: k) (x2 :: k).
----    SDecide k =>
----    Knowledge d1 x1 -> Knowledge d2 x2 -> Maybe (x1 :~: x2)
----sameKnowlege KnowledgeU KnowledgeU = Just (unsafeCoerce Refl)  -- TODO: unsafeCoerce!! Replace with coerce??
----sameKnowlege KnowledgeU (KnowledgeK s) = Just (unsafeCoerce Refl)  -- TODO: same!
----sameKnowlege (KnowledgeK s) KnowledgeU = Just (unsafeCoerce Refl)  -- TODO: same!
----sameKnowlege (KnowledgeK s1) (KnowledgeK s2) =
----    case s1 %~ s2 of
----        Proved r -> Just r
----        Disproved f -> Nothing
--
----samePartialKnowlege :: PartialKnowledge k1 x1 -> PartialKnowledge k2 x2 -> Maybe (x1 :~: x2)
----samePartialKnowlege = undefined
--
---- TODO: This one is just 1-variable. Need something like the above for multi-variable.
--instance (DepKDeserialize l, DepKDeserialize r, SDecide a) => DepKDeserialize ((l :: a -> Type) K.:*: (r :: a -> Type)) where
--    type TaughtBy ((l :: a -> Type) K.:*: (r :: a -> Type)) ds = TaughtBy r (TaughtBy l ds)
--    depKDeserialize (PartialKnowledgeCons k PartialKnowledgeNil) bs =
--        case depKDeserialize @(a -> Type) @l (PartialKnowledgeCons k PartialKnowledgeNil) bs of
--            (PartiallyKnownCons (k' :: Knowledge _ x1) (PartiallyKnownNil l), bs') ->
--                case depKDeserialize @(a -> Type) @r (PartialKnowledgeCons k' PartialKnowledgeNil) bs' of
--                    (PartiallyKnownCons (k'' :: Knowledge _ x2) (PartiallyKnownNil r), bs'') ->
--                        case sameKnowlege k' k'' :: Maybe (x1 :~: x2) of
--                            Nothing -> error "Conflicting knowledge"
--                            Just Refl ->
--                                (PartiallyKnownCons k'' (PartiallyKnownNil (l K.:*: r)), bs'')
--tryIt =
--    case depKDeserialize @(Nat -> Type) @(Sing K.:*: Vector Word8) (PartialKnowledgeCons KnowledgeU PartialKnowledgeNil) [2,3,4] of
--        (PartiallyKnownCons (KnowledgeK s) (PartiallyKnownNil p), bs) ->
--            show (p, bs)
--shouldFail =
--    case depKDeserialize @(Nat -> Type) @(Sing K.:*: Sing) (PartialKnowledgeCons KnowledgeU PartialKnowledgeNil) [2,3,4] of
--        (PartiallyKnownCons (KnowledgeK s) (PartiallyKnownNil p), bs) ->
--            show (p, bs)

newtype Wrap0 f where
    Wrap0 :: f -> Wrap0 f
newtype Curry0 f where
    Curry0 :: f K.LoT0 -> Curry0 f
data Uncurry0 f xs where
    Uncurry0 :: f -> Uncurry0 f K.LoT0
newtype Wrap1 f a where
    Wrap1 :: f a -> Wrap1 f a
newtype Curry1 f a where
    Curry1 :: f (a K.:&&: K.LoT0) -> Curry1 f a
data Uncurry1 f xs where
    Uncurry1 :: f a -> Uncurry1 f (a K.:&&: K.LoT0)
newtype Wrap2 f a b where
    Wrap2 :: f a b -> Wrap2 f a b
newtype Curry2 f a b where
    Curry2 :: f (a K.:&&: b K.:&&: K.LoT0) -> Curry2 f a b
data Uncurry2 f xs where
    Uncurry2 :: f a b -> Uncurry2 f (a K.:&&: b K.:&&: K.LoT0)
newtype Wrap3 f a b c where
    Wrap3 :: f a b c -> Wrap3 f a b c
newtype Curry3 f a b c where
    Curry3 :: f (a K.:&&: b K.:&&: c K.:&&: K.LoT0) -> Curry3 f a b c
data Uncurry3 f xs where
    Uncurry3 :: f a b c -> Uncurry3 f (a K.:&&: b K.:&&: c K.:&&: K.LoT0)
newtype Wrap4 f a b c d where
    Wrap4 :: f a b c d -> Wrap4 f a b c d
newtype Curry4 f a b c d where
    Curry4 :: f (a K.:&&: b K.:&&: c K.:&&: d K.:&&: K.LoT0) -> Curry4 f a b c d
data Uncurry4 f xs where
    Uncurry4 :: f a b c d -> Uncurry4 f (a K.:&&: b K.:&&: c K.:&&: d K.:&&: K.LoT0)

newtype UncurryK f xs where
    UncurryK :: f K.:@@: xs -> UncurryK f xs

data SingK (size :: Nat) = SingK
    { size :: Sing size
    } deriving (GHC.Generic, Show)
      --deriving DepKDeserialize via Wrap1 SingK
      -- TODO: SingK itself doesn't have a kind that DepKDeserializeK accepts... Whoops!
instance K.GenericK SingK (size K.:&&: K.LoT0) where
    type RepK SingK = K.Field (Sing K.:$: K.Var0)


f1 :: K.Field (K.Kon Sing K.:@: K.Var K.VZ) (1 K.:&&: K.LoT0)
f1 = K.Field SNat

f2 :: K.Field (K.Kon Sing K.:@: K.Var K.VZ) (2 K.:&&: 3 K.:&&: K.LoT0)
f2 = K.Field SNat

f5 :: K.Field (K.Kon Sing K.:@: K.Var (K.VS K.VZ)) (4 K.:&&: 5 K.:&&: K.LoT0)
f5 = K.Field SNat



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

--xyzf :: forall k1 k2 size1 size2 vars t1 t2 t3 t4 f3 f4.
--    (SingKind k1, SingKind k2,
--         Interpret t1 vars ~ Sing (size1 :: k1), Interpret t2 vars ~ Sing (size2 :: k2), Interpret t3 vars ~ f3 size1, Interpret t4 vars ~ f4 size2) =>
--                       (((Field t1 :*: Field t2) :*: (Field t3 :*: Field t4)) vars, [Word8])
--                       -> (Demote k1, Demote k2, Some1 f3, Some1 f4)
--xyzf ((Field a :*: Field b) :*: (Field c :*: Field d), bs) = (FromSing a, FromSing b, Some1 a c, Some1 b d)
--xyz = deserializeThisCPS [1,2,3,4,5] xyzf


class ConditionalSingIConstraint s a => ConditionalSingI (s :: Bool) (a :: k) where
    type ConditionalSingIConstraint s a :: Constraint
    maybeSameType :: Sing x -> Decision (a :~: x)
instance (SDecide k, SingI (a :: k)) => ConditionalSingI 'True a where
    type ConditionalSingIConstraint 'True a = (SDecide k, SingI (a :: k))
    maybeSameType s = sing @a %~ s
instance ()      => ConditionalSingI 'False a where
    type ConditionalSingIConstraint 'False a = ()
    maybeSameType (s :: Sing x) = Proved (unsafeCoerce Refl :: a :~: x)  -- TODO: unsafeCoerce!!

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


class {-KDeserializeConstraint f vars =>-} KDeserialize f (vars :: LoT ks) where
    --type KDeserializeConstraint f :: LoT ks -> Constraint
    --kdeserialize :: forall r. ((f vars, [Word8]) -> r) -> [Word8] -> r
instance (SingKind k, SDecide k, Serialize (Demote k), ConditionalSingI s (Interpret ('Var v) vars)) => KDeserialize (Field (Kon (Sing :: k -> Type) :@: Var v)) vars where
    --type KDeserializeConstraint (Field (Kon (Sing :: k -> Type) :@: Var v)) vars = ConditionalSingI s (Interpret ('Var v) vars)
    --kdeserialize = deserializeSing @k @v @s @vars
--instance ConditionalSingI 'True (Interpret ('Var v) vars) => KDeserialize (Field (Kon Vector :@: Kon Word8 :@: Var v)) vars where
--    kdeserialize = deserializeVector @v @vars
--instance KDeserialize (f :*: g) vars where
--    kdeserialize = undefined  -- TODO: Any hope that this can be written?


data DepStateList d where
    DZ :: DepStateList Type
    DS :: DepState -> DepStateList xs -> DepStateList (x -> xs)

type family
    LearnIth (i :: TyVar d k) (as :: DepStateList d) :: DepStateList d where
    LearnIth 'VZ ('DS _ as) = 'DS 'Known as
    LearnIth ('VS i) ('DS a as) = 'DS a (LearnIth i as)

data ExplicitPartialKnowledge (ks :: Type) (xs :: LoT ks) (ds :: DepStateList ks) where
    ExplicitPartialKnowledgeNil  :: ExplicitPartialKnowledge Type LoT0 'DZ
    ExplicitPartialKnowledgeCons :: Knowledge d (x :: a) -> ExplicitPartialKnowledge ks xs ds -> ExplicitPartialKnowledge (a -> ks) (x :&&: xs) ('DS d ds)

data PartiallyKnownK (ks :: Type) (f :: LoT ks -> Type) (ds :: DepStateList ks) where
    PartiallyKnownK :: ExplicitPartialKnowledge ks xs ds -> f xs -> PartiallyKnownK ks f ds
--instance DepKDeserialize ((l :: K.LoT ks -> Type) K.:*: (r :: K.LoT ks -> Type)) where
--    type TaughtBy ((l :: K.LoT ks -> Type) K.:*: (r :: K.LoT ks -> Type)) ds = TaughtBy r (TaughtBy l ds)
--    depKDeserialize (PartialKnowledgeCons s PartialKnowledgeNil) bs = undefined


myDemote :: forall k (a :: k). SingKind k => Sing a -> Demote k
myDemote s = withSingI s (demote @a)

vectorToList :: Vector a n -> [a]
vectorToList Nil = []
vectorToList (a :> as) = a : vectorToList as

class PartialKnowledgeToSomeSing (v :: TyVar ks k) (ds :: DepStateList ks) where
    partialKnowledgeToSomeSing :: forall xs. ExplicitPartialKnowledge ks xs ds -> SomeSing k
instance PartialKnowledgeToSomeSing 'VZ ('DS 'Known ds) where
    partialKnowledgeToSomeSing a =
        case a of
            ExplicitPartialKnowledgeCons (KnowledgeK s) _ ->
                SomeSing s
instance PartialKnowledgeToSomeSing v ds => PartialKnowledgeToSomeSing ('VS (v :: TyVar ks k)) ('DS knwlg (ds :: DepStateList ks)) where
    partialKnowledgeToSomeSing a =
        case a of
            ExplicitPartialKnowledgeCons _ knwlg ->
                partialKnowledgeToSomeSing @ks @k @v knwlg

partiallyKnownToSomeSing :: forall (v :: TyVar ks k) f ds. PartialKnowledgeToSomeSing v ds => PartiallyKnownK ks f ds -> SomeSing k
partiallyKnownToSomeSing a =
    case a of
        PartiallyKnownK knowledge _ ->
            partialKnowledgeToSomeSing @ks @k @v knowledge


examplePartiallyKnownSingVar2 :: PartiallyKnownK (k -> Nat -> Type) (Field (Kon (Sing :: Nat -> Type) :@: Var ('VS 'VZ))) ('DS 'Unknown ('DS 'Known 'DZ))
examplePartiallyKnownSingVar2 = PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeK SNat) ExplicitPartialKnowledgeNil)) (Field (SNat @1337))

examplePartiallyKnownSingVar2Unknown :: PartiallyKnownK (k -> Nat -> Type) (Field (Kon (Sing :: Nat -> Type) :@: Var ('VS 'VZ))) ('DS 'Unknown ('DS 'Unknown 'DZ))
examplePartiallyKnownSingVar2Unknown = PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeU) ExplicitPartialKnowledgeNil)) (Field (SNat @1337))

examplePartiallyKnownVecVar2 :: PartiallyKnownK (k -> Nat -> Type) (Field (Kon (Vector Word8 :: Nat -> Type) :@: Var ('VS 'VZ))) ('DS 'Unknown ('DS 'Known 'DZ))
examplePartiallyKnownVecVar2 = PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeK SNat) ExplicitPartialKnowledgeNil)) (Field (0 :> 1 :> Nil))

examplePartiallyKnownVecVar2Unknown :: PartiallyKnownK (k -> Nat -> Type) (Field (Kon (Vector Word8 :: Nat -> Type) :@: Var ('VS 'VZ))) ('DS 'Unknown ('DS 'Unknown 'DZ))
examplePartiallyKnownVecVar2Unknown = PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeU) ExplicitPartialKnowledgeNil)) (Field (0 :> 1 :> Nil))

-- Can do:
getKnownExampleSing :: SomeSing Nat
getKnownExampleSing = partiallyKnownToSomeSing @_ @_ @('VS 'VZ) examplePartiallyKnownSingVar2

getKnownExampleVec :: SomeSing Nat
getKnownExampleVec = partiallyKnownToSomeSing @_ @_ @('VS 'VZ) examplePartiallyKnownVecVar2

-- Can't do:
--getUnknownExampleSing :: SomeSing Nat
--getUnknownExampleSing = partiallyKnownToSomeSing @_ @_ @('VS 'VZ) examplePartiallyKnownSingVar2Unknown
--
--getUnknownExampleList :: SomeSing Nat
--getUnknownExampleList = partiallyKnownToSomeSing @_ @_ @('VS 'VZ) examplePartiallyKnownVecVar2Unknown


class MergePartialKnowledge (ds1 :: DepStateList ks) (ds2 :: DepStateList ks) where
    type MergedPartialKnowledge ds1 ds2 :: DepStateList ks
    mergePartialKnowledge :: forall xs. ExplicitPartialKnowledge ks xs ds1 -> ExplicitPartialKnowledge ks xs ds2 -> ExplicitPartialKnowledge ks xs (MergedPartialKnowledge ds1 ds2)
instance MergePartialKnowledge 'DZ 'DZ where
    type MergedPartialKnowledge 'DZ 'DZ = 'DZ
    mergePartialKnowledge ExplicitPartialKnowledgeNil ExplicitPartialKnowledgeNil = ExplicitPartialKnowledgeNil
instance MergePartialKnowledge ds1 ds2 => MergePartialKnowledge ('DS 'Unknown ds1) ('DS 'Unknown ds2) where
    type MergedPartialKnowledge ('DS 'Unknown ds1) ('DS 'Unknown ds2) = 'DS 'Unknown (MergedPartialKnowledge ds1 ds2)
    mergePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU ks1) (ExplicitPartialKnowledgeCons KnowledgeU ks2) =
        ExplicitPartialKnowledgeCons KnowledgeU (mergePartialKnowledge ks1 ks2)
instance MergePartialKnowledge ds1 ds2 => MergePartialKnowledge ('DS 'Known ds1) ('DS 'Unknown ds2) where
    type MergedPartialKnowledge ('DS 'Known ds1) ('DS 'Unknown ds2) = 'DS 'Known (MergedPartialKnowledge ds1 ds2)
    mergePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s) ks1) (ExplicitPartialKnowledgeCons KnowledgeU ks2) =
        ExplicitPartialKnowledgeCons (KnowledgeK s) (mergePartialKnowledge ks1 ks2)
instance MergePartialKnowledge ds1 ds2 => MergePartialKnowledge ('DS 'Unknown ds1) ('DS 'Known ds2) where
    type MergedPartialKnowledge ('DS 'Unknown ds1) ('DS 'Known ds2) = 'DS 'Known (MergedPartialKnowledge ds1 ds2)
    mergePartialKnowledge (ExplicitPartialKnowledgeCons KnowledgeU ks1) (ExplicitPartialKnowledgeCons (KnowledgeK s) ks2) =
        ExplicitPartialKnowledgeCons (KnowledgeK s) (mergePartialKnowledge ks1 ks2)
instance SDecide k => MergePartialKnowledge ds1 ds2 => MergePartialKnowledge ('DS 'Known (ds1 :: DepStateList (k -> ks))) ('DS 'Known ds2) where
    type MergedPartialKnowledge ('DS 'Known ds1) ('DS 'Known ds2) = 'DS 'Known (MergedPartialKnowledge ds1 ds2)
    mergePartialKnowledge (ExplicitPartialKnowledgeCons (KnowledgeK s1) ks1) (ExplicitPartialKnowledgeCons (KnowledgeK s2) ks2) =
        case s1 %~ s2 of
            _ ->
                ExplicitPartialKnowledgeCons (KnowledgeK s1) (mergePartialKnowledge ks1 ks2)

--class DepKDeserializeK (f :: K.LoT ks -> Type) where
--    type TaughtByK (f :: K.LoT ks -> Type) (ds :: DepStateList ks) :: DepStateList ks
--    -- TODO: Could xs go into PartiallyKnownK too? Making it ExplicitPartiallyKnown. Existentializing maybe necessary in output type...?
--    depKDeserializeK :: Proxy ks -> ExplicitPartialKnowledge ks xs ds -> [Word8] -> (PartiallyKnownK ks f (TaughtByK f ds), [Word8])
--
--
--learnIth :: forall ks k (v :: TyVar ks k) (a :: k) xs ds. Proxy ks -> Sing a -> ExplicitPartialKnowledge ks xs ds -> ExplicitPartialKnowledge ks xs (LearnIth v ds)
--learnIth = undefined
--
---- TODO: Get rid of (v ~ 'VS 'VZ), of course!
--instance (SingKind k, Serialize (Demote k), v ~ 'VS 'VZ) => DepKDeserializeK (Field (Kon (Sing :: k -> Type) :@: Var v)) where
--    type TaughtByK (Field (Kon (Sing :: k -> Type) :@: Var v)) ds = LearnIth v ds
--    depKDeserializeK p ds@(ExplicitPartialKnowledgeCons k1 (ExplicitPartialKnowledgeCons _ ExplicitPartialKnowledgeNil)) bs =
--        case deserialize bs of
--            (FromSing (s :: Sing (x :: k)), bs') ->
----                (PartiallyKnownK (ExplicitPartialKnowledgeCons k1 (ExplicitPartialKnowledgeCons (KnowledgeK s) ExplicitPartialKnowledgeNil)) (Field s), bs')
--              (PartiallyKnownK (learnIth @_ @k @v @x p s ds) (Field s), bs')
--
--
--trySingK :: String  -- Why is annotation neccessary? Why are you doing this, type families!!?!??
--trySingK =
--    case depKDeserializeK @(Nat -> Nat -> Type) @(Field (Kon Sing :@: Var ('VS 'VZ))) (Proxy @(Nat -> Nat -> Type)) (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil)) [2,3,4] of
--        (PartiallyKnownK (ExplicitPartialKnowledgeCons KnowledgeU (ExplicitPartialKnowledgeCons (KnowledgeK s) ExplicitPartialKnowledgeNil)) (Field p), bs) ->
--            show (p, bs)

{-
instance Serialize t => DepKDeserializeK (GenericKWrapper (Vector t)) where
    type TaughtByK (GenericKWrapper (Vector t)) '[ 'Known] = '[ 'Known]
    depKDeserializeK (ExplicitPartialKnowledgeCons (KnowledgeK (SNat :: Sing x)) ExplicitPartialKnowledgeNil) bs =
        case deserialize @(Vector t x) bs of
            (a, bs') ->
                (PartiallyKnownK (ExplicitPartialKnowledgeCons (KnowledgeK (SNat :: Sing x)) ExplicitPartialKnowledgeNil) (GenericKWrapper a), bs')
tryVectorK :: String
tryVectorK =
    case depKDeserializeK @(Nat -> Type) @(GenericKWrapper (Vector Word8)) (ExplicitPartialKnowledgeCons (KnowledgeK (SNat @2)) ExplicitPartialKnowledgeNil) [2,3,4] of
        (PartiallyKnownK (ExplicitPartialKnowledgeCons (KnowledgeK s) ExplicitPartialKnowledgeNil) (GenericKWrapper p), bs) ->
            show (p, bs)

instance (DepKDeserializeK l, DepKDeserializeK r) => DepKDeserializeK ((l :: K.LoT ks -> Type) K.:*: (r :: K.LoT ks -> Type)) where
    type TaughtByK ((l :: K.LoT ks -> Type) K.:*: (r :: K.LoT ks -> Type)) ds = TaughtByK r (TaughtByK l ds)

    --depKDeserializeK ExplicitPartialKnowledgeNil bs =
    --    case depKDeserializeK @Type @l ExplicitPartialKnowledgeNil bs of
    --        (PartiallyKnownK ExplicitPartialKnowledgeNil l, bs') ->
    --            case depKDeserializeK @Type @r ExplicitPartialKnowledgeNil bs' of
    --                (PartiallyKnownK ExplicitPartialKnowledgeNil r, bs'') ->
    --                    (PartiallyKnownK ExplicitPartialKnowledgeNil (l K.:*: r), bs'')
    --
    --depKDeserializeK (ExplicitPartialKnowledgeCons k ks :: ExplicitPartialKnowledge ks xs0 ds) bs =
    --    case depKDeserializeK @ks @l (ExplicitPartialKnowledgeCons k ks) bs of
    --        (PartiallyKnownK (ExplicitPartialKnowledgeCons k' ks' :: ExplicitPartialKnowledge ks xs1 (TaughtByK l ds)) l, bs') ->
    --            case depKDeserializeK @ks @r (ExplicitPartialKnowledgeCons k' ks') bs' of
    --                (PartiallyKnownK (ExplicitPartialKnowledgeCons k'' ks'' :: ExplicitPartialKnowledge ks xs2 (TaughtByK r (TaughtByK l ds))) r, bs'') ->
    --                    case unsafeCoerce Refl :: xs1 :~: xs2 of  -- TODO: I'm cheating!
    --                        Refl ->
    --                            (PartiallyKnownK (ExplicitPartialKnowledgeCons k'' ks'') (l K.:*: r), bs'')

    depKDeserializeK (ks :: ExplicitPartialKnowledge ks xs ds) bs =
        case depKDeserializeK @ks @l ks bs of
            (PartiallyKnownK (ks' :: ExplicitPartialKnowledge ks xs' (TaughtByK l ds)) l, bs') ->
                case depKDeserializeK @ks @r ks' bs' of
                    (PartiallyKnownK (ks'' :: ExplicitPartialKnowledge ks xs'' (TaughtByK r (TaughtByK l ds))) r, bs'') ->
                        case unsafeCoerce Refl :: xs' :~: xs'' of  -- TODO: I'm cheating!
                            Refl ->
                                (PartiallyKnownK ks'' (l K.:*: r), bs'')

tryItAgain :: String
tryItAgain =
    case depKDeserializeK @(Nat -> Type) @(GenericKWrapper Sing K.:*: GenericKWrapper (Vector Word8)) (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil) [2,3,4] of
        (PartiallyKnownK (ExplicitPartialKnowledgeCons (KnowledgeK s) ExplicitPartialKnowledgeNil) (GenericKWrapper sng K.:*: GenericKWrapper vec), bs) ->
            show (sng, vec, bs)
shouldFailAgain :: String
shouldFailAgain =  -- TODO: BUG: 2 ist't 3...
    case depKDeserializeK @(Nat -> Type) @(GenericKWrapper Sing K.:*: GenericKWrapper Sing) (ExplicitPartialKnowledgeCons KnowledgeU ExplicitPartialKnowledgeNil) [2,3,4] of
        (PartiallyKnownK (ExplicitPartialKnowledgeCons (KnowledgeK s) ExplicitPartialKnowledgeNil) (GenericKWrapper sng1 K.:*: GenericKWrapper sng2), bs) ->
            show (sng1, sng2, bs)
-}

















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

--exampleOfLearning :: (SingKind k, Serialize (Demote k)) => [Word8] -> (SomeDep1 'Known (Sing :: k -> Type), [Word8])
--exampleOfLearning bs =
--    case deserialize bs of
--        (Some1 _ (s :: Sing x), bs') ->
--            withSingI s (SomeDep1 @'Known @Sing @x sing, bs')
--learnedFromExample :: (SomeDep1 'Known (Sing :: Nat -> Type), [Word8])
--learnedFromExample = exampleOfLearning [5]

--deserializeDep :: forall d f. [Word8] -> (SomeDep1 (ApplyDepLevel (DepLevelOf f) d) f, [Word8])
--deserializeDep = undefined
----deserializeDep bs =
----    case deserialize bs of
----        (a, bs') ->
----            (SomeDep1 a, bs')

--class DeserializeDep1 (f :: k -> Type) where
--    deserializeDep1 :: forall d. [Word8] -> (SomeDep1 (ApplyDepLevel (DepLevelOf f) d) f, [Word8])
--instance Serialize (SomeDep1 'Known Sing) where
--    -- TODO
--instance DeserializeDep1 (Sing :: Nat -> Type) where
--    deserializeDep1 bs =
--        case deserialize bs of
--            (SomeDep1 a :: SomeDep1 'Known Sing, bs') ->
--                (SomeDep1 a, bs')
--class DeserializeDep1 (d :: DepState) (f :: k -> Type) where
--    deserializeDep1 :: Knowledge d x => [Word8] -> (SomeDep1 (ApplyDepLevel (DepLevelOf f) d) f, [Word8])
--instance (forall x. SingI x => Serialize (f x)) => DeserializeDep1 'Known f where
--    deserializeDep1 :: SingI x => [Word8] -> (SomeDep1 (ApplyDepLevel (DepLevelOf f) 'Known) f, [Word8])
--    deserializeDep1 bs = undefined
--        case deserialize bs of
--            (a, bs') ->
--                (SomeDep1 a, bs')
--instance DeserializeDep1 'Unknown (Sing :: Nat -> Type) where
--    deserializeDep1 bs =
--        case deserialize bs of
--            (Some1 SNat a, bs') ->
--                (SomeDep1 a, bs')

--type family
--    Knowledge' (s :: Maybe k) (a :: k) :: Constraint where
--    Knowledge' 'Nothing _ = ()
--    Knowledge' ('Just a) b = (a ~ b, SingI b)
--data SomeDep2' :: Maybe a -> Maybe b -> (a -> b -> Type) -> Type where
--    SomeDep2' :: forall d1 d2 f x y. (Knowledge' d1 x, Knowledge' d2 y) => f x y -> SomeDep2' d1 d2 f
--deriving instance (forall a b. Show (f a b)) => Show (SomeDep2' d1 d2 f)
--type family
--    ApplyDepLevel' (f :: DepLevel) (a :: Maybe k) :: Maybe k where
--    ApplyDepLevel' 'Requiring 'Nothing = Error "Required type index not known"
--    ApplyDepLevel' 'Requiring ('Just a) = 'Just a
--    ApplyDepLevel' 'NonDep 'Nothing = 'Nothing
--    ApplyDepLevel' 'NonDep ('Just a) = 'Just a
--    ApplyDepLevel' 'Learning 'Nothing = 'Just ???
--    ApplyDepLevel' 'Learning ('Just a) = 'Just a
--sd2'uu = SomeDep2' @'Nothing @'Nothing $ TwoVar SNat SNat (0 :> Nil) Nil
--sd2'kk = SomeDep2' @('Just 1) @('Just 0) $ TwoVar SNat SNat (0 :> Nil) Nil
--_ = case sd2'kk of SomeDep2' (_ :: TwoVar a b) -> SomeSing (sing @a)
----_ = case sd2'uu of SomeDep2' (_ :: TwoVar a b) -> SomeSing (sing @a)

--class DepDeserialize2 (f :: a -> b -> Type) where
--    type Req2 f (x :: a) (y :: b) :: Constraint
--    type Lrn2 f (x :: a) (y :: b) :: Constraint
--    depDeserialize2 :: forall r. (forall x y. Req2 f x y) => [Word8] -> (forall x y. Lrn2 f x y => (f x y, [Word8]) -> r) -> r


data Visibility a = Exposed a | Hidden
type family
    Knowledge'' (s :: Visibility k) (a :: k) :: Constraint where
    Knowledge'' 'Hidden a = SingI a
    Knowledge'' ('Exposed a) b = a ~ b
data SomeDep2'' :: (a -> b -> Type) -> Visibility a -> Visibility b -> Type where
    SomeDep2'' :: forall d1 d2 f x y. (Knowledge'' d1 x, Knowledge'' d2 y) => f x y -> SomeDep2'' f d1 d2
deriving instance (forall a b. Show (f a b)) => Show (SomeDep2'' f d1 d2)


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
--instance (Dep2Deserialize l, Dep2Deserialize r) => Dep2Deserialize (Prod2 l r) where
--    type DepLevel1 (Prod2 l r) = ProductDepLevel (DepLevel1 l) (DepLevel1 r)
--    --dep2deserialize :: forall x y. (Knowledge' (DepLevel1 (Prod2 l r)) x, Knowledge' (DepLevel2 (Prod2 l r)) y) => [Word8] -> (SomeDep2'' (Visibility' (DepLevel1 (Prod2 l r)) x) (Visibility' (DepLevel2 (Prod2 l r)) y) (Prod2 l r), [Word8])
--    dep2deserialize bs = undefined
--        --case deserialize @(SomeDep2'' (Visibility1 l x) (Visibility2 l y) l) bs of
--        --    (SomeDep2'' a, bs') ->
--        --        (undefined, bs')

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


type family
    ProductDepLevel (l :: DepLevel) (r :: DepLevel) :: DepLevel where
    ProductDepLevel 'Requiring 'Requiring = 'Requiring
    ProductDepLevel 'Requiring 'NonDep    = 'Requiring
    ProductDepLevel 'Requiring 'Learning  = 'Requiring
    ProductDepLevel 'NonDep    'Requiring = 'Requiring
    ProductDepLevel 'NonDep    'NonDep    = 'NonDep
    ProductDepLevel 'NonDep    'Learning  = 'Learning
    ProductDepLevel 'Learning  'Requiring = 'Learning
    ProductDepLevel 'Learning  'NonDep    = 'Learning
    ProductDepLevel 'Learning  'Learning  = 'Learning
class HasDepLevel (f :: k -> Type) where
    type DepLevelOf f :: DepLevel
    --type DepLevelOf f = DepLevelOf (GHC.Rep1 f)
    type DepLevelOf f = DepLevelOf (K.RepK f)
-- GHC.Generic instances
instance HasDepLevel GHC.U1 where
    type DepLevelOf GHC.U1 = 'NonDep
instance HasDepLevel (GHC.Rec0 c) where
    type DepLevelOf (GHC.Rec0 c) = 'NonDep
instance HasDepLevel (GHC.K1 i c) where
    type DepLevelOf (GHC.K1 i c) = 'NonDep
instance HasDepLevel (GHC.Rec1 f) where
    type DepLevelOf (GHC.Rec1 f) = DepLevelOf f
instance HasDepLevel (GHC.S1 c f) where
    type DepLevelOf (GHC.S1 c f) = DepLevelOf f
instance HasDepLevel (GHC.M1 i c f) where
    type DepLevelOf (GHC.M1 i c f) = DepLevelOf f
instance HasDepLevel (l GHC.:*: r) where
    type DepLevelOf (l GHC.:*: r) = ProductDepLevel (DepLevelOf l) (DepLevelOf r)
--
instance HasDepLevel Sing where
    type DepLevelOf Sing = 'Learning
instance HasDepLevel (Vector a) where
    type DepLevelOf (Vector a) = 'Requiring
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

instance {-# OVERLAPS #-} (Product1Serialize (DepLevelOf f) (DepLevelOf g) f g) => Serialize (Some1 ((f :: K.LoT (a -> Type) -> Type) GHC.:*: g)) where
    serialize a = p1serialize @_ @(DepLevelOf f) @(DepLevelOf g) a
    deserialize bs = p1deserialize @_ @(DepLevelOf f) @(DepLevelOf g) bs


instance SingI a => Serialize (Sing (a :: Fin n)) where  -- 8-bit
    serialize SFin = [fromIntegral $ finVal @a]
    deserialize (a : bs) =
        withKnownFin @a sing $
            if fromIntegral a == finVal @a then
                (SFin, bs)
            else
                error "Deserialized wrong SNat"
--instance SingI n => Serialize (SomeSing (Fin n)) where
--    serialize (SomeSing (SFin :: Sing a)) = serialize (SFin @n @a)
--    deserialize bs =
--        case deserialize bs of
--            (n :: Word8, bs') ->
--                case sing @n of
--                    SNat ->
--                        case someFinVal (fromIntegral n) of
--                            Nothing -> error $ show n ++ " out of bounds for Fin"  -- TODO: Not like this!
--                            Just (SomeFin (Proxy :: Proxy a)) ->
--                                (SomeSing @(Fin n) @a SFin, bs')
--instance Serialize (Fin n) where
--    serialize a = undefined
--    deserialize bs = undefined
--data IndexedOnFin256 (size :: Fin 256) = IndexedOnWord8
--    { x :: Sing size
--    --, arr :: Vector Word8 size
--    } deriving (GHC.Generic1, Show, HasDepLevel, Serialize)
--
--diow8 :: Some1 IndexedOnFin256
--diow8 = fst $ deserializeSome1 [1]
--siow8 :: [Word8]
--siow8 = serializeSome1 diow8

newtype GenericKWrapper f a = GenericKWrapper { unwrapGenericK :: f K.:@@: a }
instance (K.GenericK f x, Serialize (K.RepK f x), HasDepLevel f) => Serialize (GenericKWrapper f x) where
    serialize (GenericKWrapper a) = serialize $ K.fromK @_ @f @x a
    deserialize bs =
        case deserialize bs of
            (a, bs') ->
                (GenericKWrapper (K.toK @_ @f @x a), bs')
--newtype Generic1KWrapper f a = Generic1KWrapper { unwrapGeneric1K :: f K.:@@: (a K.:&&: K.LoT0) }
--instance (K.GenericK f (a K.:&&: K.LoT0), Serialize (K.RepK f (a K.:&&: K.LoT0)), HasDepLevel f) => Serialize (Generic1KWrapper f a) where
--    serialize (Generic1KWrapper a) = serialize $ K.fromK @_ @f @(a K.:&&: K.LoT0) a
--    deserialize bs =
--        case deserialize bs of
--            (a, bs') ->
--                (Generic1KWrapper (K.toK @_ @f @(a K.:&&: K.LoT0) a), bs')

instance Serialize (f (K.Interpret (K.Var K.VZ) xs)) => Serialize (K.Field (f K.:$: K.Var0) xs) where
    serialize (K.Field a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (K.Field a, bs')
instance Serialize a => Serialize (K.Field ('K.Kon a) vs) where
    serialize (K.Field a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (K.Field a, bs')

--newtype Rep1K :: (k -> Type) -> k -> Type where
--    Rep1K :: K.RepK f (a K.:&&: K.LoT0) -> Rep1K f a
--serializeSome1K :: forall f. (forall x. K.GenericK f (x K.:&&: K.LoT0), Serialize (Some1 (Rep1K f))) => Some1 f -> [Word8]
--serializeSome1K (Some1 s a) = serialize (Some1 s (Rep1K @f (K.fromK a)))
--deserializeSome1K :: forall f. (forall x. K.GenericK f (x K.:&&: K.LoT0), Serialize (Some1 (Rep1K f))) => [Word8] -> (Some1 f, [Word8])
--deserializeSome1K bs =
--    case deserialize bs of
--        (Some1 (s :: Sing a) (Rep1K a :: Rep1K f a), bs') ->
--            (Some1 s (K.toK a), bs')

instance HasDepLevel (K.Field (K.Kon f K.:@: K.Var K.VZ)) where
    type DepLevelOf (K.Field (K.Kon f K.:@: K.Var K.VZ)) = DepLevelOf f
--    Equivalently
--instance HasDepLevel (K.Field (f K.:$: K.Var0)) where
--    type DepLevelOf (K.Field (f K.:$: K.Var0)) = DepLevelOf f
--------------------------instance Product1Serialize
--------------------------    (DepLevelOf (GHC.Rep1 UnitWithSize))
--------------------------    (ProductDepLevel 'Learning (DepLevelOf (GHC.Rep1 RequiringSize)))
--------------------------    (K.Field (UnitWithSize K.:$: K.Var0))
--------------------------    (K.Field (Sing K.:$: K.Var0) K.:*: K.Field (RequiringSize K.:$: K.Var0))

-- TODO: Can it be written in terms of (Dict1 c (f :: Nat -> Type))?
instance (forall x. KnownNat x => c (f (x 'K.:&&: 'K.LoT0))) => Dict1 c (f :: K.LoT (Nat -> Type) -> Type) where
    dict1 (SNat :&&&: SLoT0) = Dict
infixr :&&&:
--instance Serialize (Some1 f) => Serialize (Some1 (K.Field (f K.:$: K.Var0))) where
--    serialize (Some1 (SLoT1 s) (K.Field a)) = serialize (Some1 s a)
--    deserialize bs =
--        case deserialize @(Some1 f) bs of
--            (Some1 (s :: Sing a) a :: Some1 f, bs') ->
--                (Some1 (SLoT1 s :: Sing (a K.:&&: K.LoT0)) (K.Field a :: K.Field (f K.:$: K.Var0) (a K.:&&: K.LoT0)) :: Some1 (K.Field (f K.:$: K.Var0)), bs')
--                --(Some1 (SLoT1 s :: Sing (k K.:&&: K.LoT0)) (K.Field a), bs')

instance Serialize (Some1 f) => Serialize (Some1 (K.Field ('K.Kon f 'K.:@: 'K.Var 'K.VZ :: K.Atom (k -> Type) Type))) where
    serialize (Some1 (s :&&&: SLoT0) (K.Field a)) = serialize (Some1 s a)
    deserialize bs =
        case deserialize bs of
            (Some1 s a, bs') ->
                (Some1 (s :&&&: SLoT0) (K.Field a), bs')

--instance Serialize (Some1 (K.RepK f :: K.LoT (k -> Type) -> Type)) => Serialize (Some1 (Rep1K f :: k -> Type)) where
--    serialize (Some1 s (Rep1K (a :: K.RepK f (a K.:&&: K.LoT0)) :: Rep1K f a)) = serialize (Some1 undefined a)
--    deserialize bs = undefined

data instance Sing :: K.LoT xs -> Type where
    SLoT0 :: Sing K.LoT0
    (:&&&:) :: Sing x -> Sing xs -> Sing (x K.:&&: xs)
serializeSome1K :: forall f. (forall x. K.GenericK f (x K.:&&: K.LoT0), Serialize (Some1 (K.RepK f))) => Some1 f -> [Word8]
serializeSome1K (Some1 s a) = serialize (Some1 (s :&&&: SLoT0) (K.fromK a))
deserializeSome1K :: forall f. (forall x. K.GenericK f (x K.:&&: K.LoT0), Serialize (Some1 (K.RepK f))) => [Word8] -> (Some1 f, [Word8])
deserializeSome1K bs =
    case deserialize @(Some1 (K.RepK f)) bs of
        (Some1 (s :&&&: SLoT0) a, bs') ->
            (Some1 s (K.toK a), bs')

data RequiringSize (size :: Nat) = RequiringSize
    { arr1 :: Vector Word8 size
    , arr2 :: Vector Word8 size
    } deriving (Show, HasDepLevel, GHC.Generic)
      deriving Serialize via (GenericKWrapper RequiringSize (size K.:&&: K.LoT0))
instance K.GenericK RequiringSize (size K.:&&: K.LoT0) where
    type RepK RequiringSize = K.Field (Vector Word8 K.:$: K.Var0) K.:*: K.Field (Vector Word8 K.:$: K.Var0)
--instance K.Split (RequiringSize size) RequiringSize (size K.:&&: K.LoT0)
srs :: [Word8]
srs = serialize $ RequiringSize (1 :> 2 :> 3 :> Nil) (4 :> 5 :> 6 :> Nil)
drs :: KnownNat size => (RequiringSize size, [Word8])
drs = deserialize srs

data ProvidingSize (size :: Nat) = ProvidingSize
    { uws :: UnitWithSize size
    , size :: Sing size
    , rs :: RequiringSize size
    } deriving (Show, HasDepLevel, GHC.Generic)
      deriving Serialize via (GenericKWrapper ProvidingSize (size K.:&&: K.LoT0))
instance K.GenericK ProvidingSize (size K.:&&: K.LoT0) where
    type RepK ProvidingSize = K.Field (UnitWithSize K.:$: K.Var0) K.:*: K.Field (Sing K.:$: K.Var0) K.:*: K.Field (RequiringSize K.:$: K.Var0)
--instance K.Split (ProvidingSize size) ProvidingSize (size K.:&&: K.LoT0)
sps :: [Word8]
sps = serialize $ ProvidingSize UnitWithSize SNat (RequiringSize (1 :> 2 :> 3 :> Nil) (4 :> 5 :> 6 :> Nil))
dps :: Some1 ProvidingSize
dps = fst $ deserializeSome1K sps
dps' :: KnownNat size => ProvidingSize size
dps' = fst $ deserialize sps

data IgnoringSize (size :: Nat) = IgnoringSize
    { size :: Word8
    } deriving (Show, HasDepLevel, GHC.Generic)
      deriving Serialize via (GenericKWrapper IgnoringSize (size K.:&&: K.LoT0))
instance K.GenericK IgnoringSize (size K.:&&: K.LoT0) where
    type RepK IgnoringSize = K.Field (K.Kon Word8)
--instance K.Split (IgnoringSize size) IgnoringSize (size K.:&&: K.LoT0)
sis :: [Word8]
sis = serialize $ IgnoringSize 123
dis :: IgnoringSize size
dis = fst $ deserialize sis

data UnitWithSize (size :: Nat) = UnitWithSize
    {} deriving (Show, HasDepLevel, GHC.Generic)
       deriving Serialize via (GenericKWrapper UnitWithSize (size K.:&&: K.LoT0))
instance K.GenericK UnitWithSize (size K.:&&: K.LoT0) where
    type RepK UnitWithSize = K.U1
--instance K.Split (UnitWithSize size) UnitWithSize (size K.:&&: K.LoT0)
snws :: [Word8]
snws = serialize $ UnitWithSize
dnws :: UnitWithSize size
dnws = fst $ deserialize snws





{-
class HasDepLevels (f :: K.LoT (a -> b -> Type) -> Type) where
    type DepLevelsOf f :: [DepLevel]
--instance HasDepLevels (K.Field (l K.:$: K.Var0) K.:*: K.Field (r K.:$: K.Var0)) where
--    type DepLevelsOf (K.Field (l K.:$: K.Var0) K.:*: K.Field (r K.:$: K.Var0)) = '[ProductDepLevel (DepLevelOf l) (DepLevelOf r), NonDep]
--instance HasDepLevels (K.Field (l K.:$: K.Var0) K.:*: K.Field (r K.:$: K.Var1)) where
--    type DepLevelsOf (K.Field (l K.:$: K.Var0) K.:*: K.Field (r K.:$: K.Var1)) = '[DepLevelOf l, DepLevelOf r]
--instance HasDepLevels (K.Field (l K.:$: K.Var1) K.:*: K.Field (r K.:$: K.Var0)) where
--    type DepLevelsOf (K.Field (l K.:$: K.Var1) K.:*: K.Field (r K.:$: K.Var0)) = '[DepLevelOf r, DepLevelOf l]
--instance HasDepLevels (K.Field (l K.:$: K.Var1) K.:*: K.Field (r K.:$: K.Var1)) where
--    type DepLevelsOf (K.Field (l K.:$: K.Var1) K.:*: K.Field (r K.:$: K.Var1)) = '[NonDep, ProductDepLevel (DepLevelOf l) (DepLevelOf r)]
-- And a lot more... This is a combinatorial explosion!
-- Solution? Canonicalization, perhaps?
type family DotProductDepLevel (ldeps :: [DepLevel]) (rdeps :: [DepLevel]) :: [DepLevel] where
    DotProductDepLevel '[] '[] = '[]
    DotProductDepLevel (a ': as) (b ': bs) = ProductDepLevel a b ': DotProductDepLevel as bs
instance HasDepLevels (K.Field (K.Kon l K.:@: K.Var0 K.:@: K.Var1) K.:*: K.Field (K.Kon r K.:@: K.Var0 K.:@: K.Var1)) where
    type DepLevelsOf (K.Field (K.Kon l K.:@: K.Var0 K.:@: K.Var1) K.:*: K.Field (K.Kon r K.:@: K.Var0 K.:@: K.Var1)) =
        DotProductDepLevel (DepLevelsOf (K.Field (K.Kon l K.:@: K.Var0 K.:@: K.Var1))) (DepLevelsOf (K.Field (K.Kon r K.:@: K.Var0 K.:@: K.Var1)))

class (ldeps ~ DepLevelsOf l, rdeps ~ DepLevelsOf r) => Product2Serialize (ldeps :: [DepLevel]) (rdeps :: [DepLevel]) (l :: K.LoT (a -> b -> Type) -> Type) (r :: K.LoT (a -> b -> Type) -> Type) where
    p2serialize :: Some1 (l GHC.:*: r) -> [Word8]
    p2deserialize :: [Word8] -> (Some1 (l GHC.:*: r), [Word8])
instance (ldeps ~ DepLevelsOf l, rdeps ~ DepLevelsOf r) => Product2Serialize (ldeps :: [DepLevel]) (rdeps :: [DepLevel]) (l :: K.LoT (a -> b -> Type) -> Type) (r :: K.LoT (a -> b -> Type) -> Type) where

instance {-# OVERLAPS #-} (Product2Serialize (DepLevelsOf f) (DepLevelsOf g) f g) => Serialize (Some1 ((f :: K.LoT (a -> b -> Type) -> Type) GHC.:*: g)) where
    serialize a = p2serialize @_ @_ @(DepLevelsOf f) @(DepLevelsOf g) a
    deserialize bs = p2deserialize @_ @_ @(DepLevelsOf f) @(DepLevelsOf g) bs


instance (K.GenericK f xs, Serialize (K.RepK f xs), HasDepLevels (K.RepK f)) => Serialize (GenericKWrapper f xs) where
    serialize (GenericKWrapper a) = serialize $ K.fromK @_ @f @xs a
    deserialize bs =
        case deserialize bs of
            (a, bs') ->
                (GenericKWrapper (K.toK @_ @f @xs a), bs')

instance Serialize (f (K.Interpret (K.Var (K.VS K.VZ)) (a 'K.:&&: b 'K.:&&: 'K.LoT0))) => Serialize (K.Field (f K.:$: K.Var1) (a 'K.:&&: b 'K.:&&: 'K.LoT0)) where
    serialize (K.Field a) = serialize a
    deserialize bs =
        case deserialize bs of
            (a, bs') -> (K.Field a, bs')
--instance Serialize a => Serialize (K.Field ('K.Kon a) vs) where
--    serialize (K.Field a) = serialize a
--    deserialize bs =
--        case deserialize bs of
--            (a, bs') -> (K.Field a, bs')

serializeSome2K :: forall f. (forall a b. K.GenericK f (a 'K.:&&: b 'K.:&&: 'K.LoT0), Serialize (Some1 (K.RepK f))) => Some2 f -> [Word8]
serializeSome2K (Some2 s t a) = serialize (Some1 (s :&&&: t :&&&: SLoT0) (K.fromK a))
deserializeSome2K :: forall f. (forall a b. K.GenericK f (a 'K.:&&: b 'K.:&&: 'K.LoT0), Serialize (Some1 (K.RepK f))) => [Word8] -> (Some2 f, [Word8])
deserializeSome2K bs =
    case deserialize @(Some1 (K.RepK f)) bs of
        (Some1 (s :&&&: t :&&&: SLoT0) a, bs') ->
            (Some2 s t (K.toK a), bs')

instance HasDepLevel (K.Field (K.Kon f K.:@: K.Var (K.VS K.VZ))) where
    type DepLevelOf (K.Field (K.Kon f K.:@: K.Var (K.VS K.VZ))) = DepLevelOf f

-- TODO: BUG: This is the tricky part. (F _) is parameterized on a LoT of two tyvars. So the Some1's are
-- TODO: BUG: to hold singletons for such lists. So both the vars must be known after deserialization.
-- TODO: BUG: But we're only getting info about one.
--instance Serialize (Some1 f) => Serialize (Some1 (K.Field ('K.Kon (f :: a -> Type) 'K.:@: 'K.Var 'K.VZ :: K.Atom (a -> b -> Type) Type))) where
--    serialize (Some1 (s :&&&: _ :&&&: SLoT0) (K.Field a)) = serialize (Some1 s a)
--    deserialize bs =
--        case deserialize bs of
--            (Some1 s a, bs') ->
--                (Some1 (s :&&&: undefined :&&&: SLoT0) (K.Field a), bs')
--instance Serialize (Some1 f) => Serialize (Some1 (K.Field ('K.Kon (f :: b -> Type) 'K.:@: 'K.Var ('K.VS 'K.VZ) :: K.Atom (a -> b -> Type) Type))) where
--    serialize (Some1 (_ :&&&: s :&&&: SLoT0) (K.Field a)) = serialize (Some1 s a)
--    deserialize bs =
--        case deserialize bs of
--            (Some1 s a, bs') ->
--                (Some1 (undefined :&&&: s :&&&: SLoT0) (K.Field a), bs')

-- TODO: Should be correct, but I've never been asked for this instance.
--instance Serialize (Some2 f)
--    => Serialize (Some1 (K.Field 
--        ('K.Kon (f :: a -> b -> Type) 'K.:@: 'K.Var 'K.VZ 'K.:@: 'K.Var ('K.VS 'K.VZ) :: K.Atom (a -> b -> Type) Type))) where
--    serialize (Some1 (s1 :&&&: s2 :&&&: SLoT0) (K.Field a)) = serialize (Some2 s1 s2 a)
--    deserialize bs =
--        case deserialize bs of
--            (Some2 s1 s2 a, bs') ->
--                (Some1 (s1 :&&&: s2 :&&&: SLoT0) (K.Field a), bs')


-- TODO: Not nice. Why do I even need this?
instance Show (K.LoT Type) where
    show K.LoT0 = "LoT0"
deriving instance (Show a, Show (K.LoT as)) => Show (K.LoT (a -> as))

instance SingKind (K.LoT Type) where
    type Demote (K.LoT Type) = K.LoT Type
    fromSing SLoT0 = K.LoT0
    toSing K.LoT0 = SomeSing SLoT0
-- TODO: Induction!
instance SingKind a => SingKind (K.LoT (a -> Type)) where
    type Demote (K.LoT (a -> Type)) = K.LoT (Demote a -> Type)
    fromSing (a :&&&: SLoT0) = FromSing a K.:&&: K.LoT0
    toSing (FromSing a K.:&&: K.LoT0) = SomeSing (a :&&&: SLoT0)
instance (SingKind a, SingKind b) => SingKind (K.LoT (a -> b -> Type)) where
    type Demote (K.LoT (a -> b -> Type)) = K.LoT (Demote a -> Demote b -> Type)
    fromSing (a :&&&: b :&&&: SLoT0) = FromSing a K.:&&: FromSing b K.:&&: K.LoT0
    toSing (FromSing a K.:&&: FromSing b K.:&&: K.LoT0) = SomeSing (a :&&&: b :&&&: SLoT0)

instance SDecide (K.LoT Type) where
    SLoT0 %~ SLoT0 = Proved Refl
instance (SDecide a, SDecide (K.LoT as)) => SDecide (K.LoT (a -> as)) where
    (a :&&&: as) %~ (b :&&&: bs) =
        case a %~ b of
            Disproved f -> Disproved (f . toHead)
            Proved Refl ->
                case as %~ bs of
                    Disproved f -> Disproved (f . toTail)
                    Proved Refl ->
                        Proved Refl
        where
            toHead :: (x K.:&&: xs) :~: (y K.:&&: ys) -> x :~: y
            toHead Refl = Refl
            toTail :: (x K.:&&: xs) :~: (y K.:&&: ys) -> xs :~: ys
            toTail Refl = Refl

-- TODO: Inductive instance.
instance (Dict1 Serialize f, Dict1 Serialize g) => Dict1 Serialize (K.Field (f K.:$: K.Var0) K.:*: K.Field (g K.:$: K.Var1)) where
    dict1 ((s1 :: Sing a) :&&&: (s2 :: Sing b) :&&&: SLoT0) =
        withDict (dict1 s1 :: Dict (Serialize (f a))) $
            withDict (dict1 s2 :: Dict (Serialize (g b))) $
                Dict

instance (forall x y. (KnownNat x, KnownNat y) => c (f x y)) => Dict2 c (f :: Nat -> Nat -> Type) where
    dict2 SNat SNat = Dict
-- TODO: Or how about?
--instance (forall x y. (SingI x, SingI y) => c (f x y)) => Dict2 c (f :: a -> b -> Type) where
--    dict2 s1 s2 = withSingI s1 $ withSingI s2 $ Dict

data TwoVar (size1 :: Nat) (size2 :: Nat) = TwoVar
    { size1 :: Sing size1
    , size2 :: Sing size2
    , arr1  :: Vector Word8 size1
    , arr2  :: Vector Word8 size2
    } deriving (Show, GHC.Generic)
      deriving Serialize via (GenericKWrapper TwoVar (size1 K.:&&: size2 K.:&&: K.LoT0))
instance HasDepLevels ((K.Field (Sing K.:$: K.Var0) K.:*: K.Field (Sing K.:$: K.Var1)) K.:*: (K.Field (Vector Word8 K.:$: K.Var0) K.:*: K.Field (Vector Word8 K.:$: K.Var1))) where
    type DepLevelsOf ((K.Field (Sing K.:$: K.Var0) K.:*: K.Field (Sing K.:$: K.Var1)) K.:*: (K.Field (Vector Word8 K.:$: K.Var0) K.:*: K.Field (Vector Word8 K.:$: K.Var1))) = '[ 'Learning, 'Learning]
instance K.GenericK TwoVar (size1 K.:&&: size2 K.:&&: K.LoT0) where
    type RepK TwoVar = (K.Field (Sing K.:$: K.Var0) K.:*: K.Field (Sing K.:$: K.Var1)) K.:*: (K.Field (Vector Word8 K.:$: K.Var0) K.:*: K.Field (Vector Word8 K.:$: K.Var1))
instance K.Split (TwoVar size1 size2) TwoVar (size1 K.:&&: size2 K.:&&: K.LoT0)
stw :: [Word8]
stw = serialize $ TwoVar SNat SNat (1 :> Nil) (2 :> 3 :> Nil)
dtw :: Some2 TwoVar
dtw = fst $ deserializeSome2K stw
dtw' :: (KnownNat size1, KnownNat size2) => TwoVar size1 size2
dtw' = fst $ deserialize stw

--data Fst (f :: k -> Type) (p :: (k, k2)) where
--    Fst :: f a -> Fst f '(a, b)
--instance ForallF Show f => Show (Fst f p) where
--    show (Fst (a :: f a)) = "Fst (" ++ (show a \\ instF @Show @f @a) ++ ")"
--
--data Snd (f :: k -> Type) (p :: (k1, k)) where
--    Snd :: f b -> Snd f '(a, b)
--instance ForallF Show f => Show (Snd f p) where
--    show (Snd (a :: f b)) = "Snd (" ++ (show a \\ instF @Show @f @b) ++ ")"
--
--data DependentMore (size1size2 :: (Nat, Nat)) = DependentMore
--    { size1 :: Fst Sing size1size2
--    , size2 :: Snd Sing size1size2
--    , arr1 :: Fst (Vector Word8) size1size2
--    , arr2 :: Snd (Vector Word8) size1size2
--    } deriving (Show, Generic1)
--
--exampleDependentMore :: DependentMore '(1, 2)
--exampleDependentMore = DependentMore (Fst SNat) (Snd SNat) (Fst (3 :> Nil)) (Snd (4 :> 5 :> Nil))
--
-- TODO: The above is seemingly the best I can get with Generic1.
-- TODO: I should look back to the ideas I had some time ago where instead of relying on Generic1 (and the Generic2... that I wish existed),
-- TODO: I rely only on Generic. Then I inject distinct values on each type variable (or element of HList/tuple) as "tags" for a TaggedHList
-- TODO: I'm simply wondering if that approach is more or less a hand-baked GenericN? That would honestly be blog post worthy...
-}


{-
instance Serialize (NP I xs) => Serialize (SOP I '[xs]) where
    serialize (SOP (Z as)) = serialize as
    deserialize bs =
        case deserialize @(NP I xs) bs of
            (as, bs') -> (SOP (Z as), bs')
instance Serialize (NP I '[]) where
    serialize SOP.Nil = []
    deserialize bs = (SOP.Nil, bs)
instance (Serialize x, Serialize (NP I xs)) => Serialize (NP I (x ': xs)) where
    serialize (I a :* as) = serialize a ++ serialize as
    deserialize bs =
        case deserialize @x bs of
            (a, bs') ->
                case deserialize @(NP I xs) bs' of
                    (b, bs'') -> (I a :* b, bs'')

data Dependency a = NonDependent | Dependent a
    deriving Show

data instance Sing :: Dependency a -> Type where
    SNonDependent :: Sing ('NonDependent :: Dependency a)
    SDependent :: Sing x -> Sing ('Dependent x :: Dependency a)
instance SingKind a => SingKind (Dependency a) where
    type Demote (Dependency a) = Dependency (Demote a)
    fromSing SNonDependent = NonDependent
    fromSing (SDependent a) = Dependent (fromSing a)
    toSing NonDependent = SomeSing SNonDependent
    toSing (Dependent (FromSing a)) = SomeSing (SDependent a)

type family (a :: t -> Type) // (b :: Dependency t) :: Type where
    Sing // ('NonDependent :: Dependency t) = Demote t
    a // 'NonDependent = Some1 a
    a // 'Dependent b = a b

data DependentMore (size1 :: Dependency Nat) (size2 :: Dependency Nat) = DependentMore
    { size1 :: Sing // size1
    , size2 :: Sing // size2
    , arr1 :: Vector Word8 // size1
    , arr2 :: Vector Word8 // size2
    } deriving (GHC.Generic, Generic)
deriving instance
    ( Show (Sing // size1)
    , Show (Sing // size2)
    , Show (Vector Word8 // size1)
    , Show (Vector Word8 // size2)
    ) => Show (DependentMore size1 size2)


type family NonDependent (a :: t) :: Type where
    NonDependent (a :: Type) = a
    NonDependent (a :: Dependency _ -> t) = NonDependent (a 'NonDependent)

exampleNonDependentMore :: NonDependent DependentMore
exampleNonDependentMore = DependentMore 1 2 (some1 (3 :> Nil)) (some1 (4 :> 5 :> Nil))

exampleDependentMore :: DependentMore ('Dependent 1) ('Dependent 2)
exampleDependentMore = DependentMore SNat SNat (3 :> Nil) (4 :> 5 :> Nil)

lols :: Rep (DependentMore ('Dependent 1) ('Dependent 2))
lols = from exampleDependentMore

slols = serialize lols
dlols :: (Rep (DependentMore ('Dependent 1) ('Dependent 2)), [Word8])
dlols = deserialize slols

lols' :: DependentMore ('Dependent 1) ('Dependent 2)
lols' = to (fst dlols)

nlols :: Rep (NonDependent DependentMore)
nlols = gundepend (fst dlols)

nlols' :: NonDependent DependentMore
nlols' = to nlols



class GUndepend' a b where
    gundepend' :: a -> b
instance GUndepend' a a where
    gundepend' a = a
instance (SingKind t, dt ~ Demote t) => GUndepend' (Sing (a :: t)) dt where
    gundepend' a = fromSing a
instance SingI n => GUndepend' (a n) (Some1 a) where
    gundepend' a = some1 a

class GUndepend a b where
    gundepend :: a -> b
instance (a ~ SOP I '[xs], b ~ SOP I '[ys], AllZip GUndepend' xs ys) => GUndepend a b where
    gundepend = htrans (Proxy @GUndepend') (\(I a) -> I (gundepend' a))

undepend1 ::
    ( Generic (a ('Dependent x))
    , Generic (NonDependent a)
    , GUndepend (Rep (a ('Dependent x))) (Rep (NonDependent a))
    ) => a ('Dependent x) -> NonDependent a
undepend1 = to . gundepend . from
undepend2 ::
    ( Generic (a ('Dependent x) ('Dependent y))
    , Generic (NonDependent a)
    , GUndepend (Rep (a ('Dependent x) ('Dependent y))) (Rep (NonDependent a))
    ) => a ('Dependent x) ('Dependent y) -> NonDependent a
undepend2 = to . gundepend . from

-- TODO: This has bad inference. For example I need to say
--           undepend @_ @(NonDependent DependentMore) exampleDependentMore
--       Otherwise, it thinks the second type's Rep is `U1` (Rep for unit) for some reason.
undepend :: forall a b. (GUndepend (Rep a) (Rep b), Generic b, Generic a) => a -> b
undepend = to . gundepend . from


data DependentPlusFree (size1 :: Dependency Nat) (size2 :: Dependency Nat) = DependentPlusFree
    { size1 :: Sing // size1
    , size2 :: Sing // size2
    , arr1 :: Vector Word8 // size1
    , arr2 :: Vector Word8 // size2
    , freeArr :: Vector Word8 4
    } deriving (GHC.Generic, Generic)
deriving instance
    ( Show (Sing // size1)
    , Show (Sing // size2)
    , Show (Vector Word8 // size1)
    , Show (Vector Word8 // size2)
    ) => Show (DependentPlusFree size1 size2)

dpf :: DependentPlusFree ('Dependent 1) ('Dependent 2)
dpf = DependentPlusFree SNat SNat (3 :> Nil) (4 :> 5 :> Nil) (6 :> 7 :> 8 :> 9 :> Nil)

ndpf :: NonDependent DependentPlusFree
ndpf = undepend dpf



class GDepend' a b where
    gdepend' :: b -> Either String a
instance GDepend' a a where
    gdepend' a = Right a
instance (SingKind t, dt ~ Demote t, SDecide t, SingI a, Show dt) => GDepend' (Sing (a :: t)) dt where
    gdepend' a =
        withSomeSing a $ \s ->
            case s %~ sing @a of
                Proved Refl ->
                    Right s
                Disproved r ->
                    -- TODO: Can probably grap field name.
                    Left ("((Sing) Refuted: " ++ show a ++ " %~ " ++ show (demote @a) ++ ")")
instance (SingKind t, SDecide t, SingI (n :: t), Show (Demote t)) => GDepend' (a n) (Some1 a) where
    gdepend' (Some1 n a) =
        case n %~ sing @n of
            Proved Refl ->
                Right a
            Disproved r ->
                -- TODO: Can probably grap field name.
                Left ("((Some1) Refuted: " ++ show (fromSing n) ++ " %~ " ++ show (demote @n) ++ ")")

class GDepend f g where
    gdepend :: g -> Either String f
instance GDepend (NP I xs) (NP I ys) => GDepend (SOP I '[xs]) (SOP I '[ys]) where
    gdepend (SOP (Z xs)) = SOP . Z <$> gdepend xs
instance GDepend (NP I '[]) (NP I '[]) where
    gdepend SOP.Nil = Right SOP.Nil
instance (GDepend (I x) (I y), GDepend (NP I xs) (NP I ys)) => GDepend (NP I (x ': xs)) (NP I (y ': ys)) where
    gdepend (a :* as) =
        case (gdepend a, gdepend as) of
            (Left s, Left t) -> Left (s ++ " :* " ++ t)
            (Left s, Right y) -> Left (s ++ " :* _")
            (Right x, Left t) -> Left ("_ :* " ++ t)
            (Right x, Right y) -> Right (x :* y)
instance GDepend' a b => GDepend (I a) (I b) where
    gdepend (I a) = I <$> gdepend' a
--instance (a ~ SOP I '[xs], b ~ SOP I '[ys], AllZip GDepend' xs ys) => GDepend a b where
--    gdepend = htrans (Proxy @GDepend') (\(I a) -> I (gdepend' a))

--class GUndepend a b where
--    gundepend :: a -> b
--instance (a ~ SOP I '[xs], b ~ SOP I '[ys], AllZip GUndepend' xs ys) => GUndepend a b where
--    gundepend = htrans (Proxy @GUndepend') (\(I a) -> I (gundepend' a))



depend :: forall a b. (GDepend (Rep a) (Rep b), Generic b, Generic a) => b -> Either String a
depend a = to <$> gdepend (from a)

redpf :: Either String (DependentPlusFree ('Dependent 1) ('Dependent 2))
redpf = depend ndpf

faileddpf :: Either String (DependentPlusFree ('Dependent 3) ('Dependent 2))
faileddpf = depend ndpf


someDpf :: Some2 DependentPlusFree
someDpf = Some2 (SDependent SNat :: Sing ('Dependent 1 :: Dependency Nat)) (SDependent SNat :: Sing ('Dependent 2 :: Dependency Nat)) dpf

--class DropDependency a where
--    dropDependency :: a p -> a p

--nonDependentRep1 :: forall a x y z. Rep (a ('Dependent x)) y -> Rep (a 'NonDependent) z
----nonDependentRep1 (M1 (M1 ((M1 (K1 size1)) :*: M1 (K1 (size2))) :*: (M1 (K1 arr1) :*: M1 (K1 arr2)))) = undefined
--nonDependentRep1 = undefined

--nonDependentMore :: Rep (DependentMore ('Dependent size1) ('Dependent size2)) p -> Rep (DependentMore 'NonDependent 'NonDependent) p
--nonDependentMore (M1 (M1 ((M1 (K1 size1)) :*: M1 (K1 (size2))) :*: (M1 (K1 arr1) :*: M1 (K1 arr2)))) = undefined

--nonDependent1K1 :: K1 () -> K1 'NonDependent

--nonDependent1 :: forall a x. (Generic (a ('Dependent x)), Generic (a 'NonDependent)) => a ('Dependent x) -> a 'NonDependent
--nonDependent1 a = to $ nonDependentRep1 @a @x $ from a


data G :: Type -> Type where
    G :: a -> G a
    Tag :: Nat -> G a

data GSing :: G t -> Type where
    GSing :: Sing (a :: t) -> GSing ('G a)
data GVector a :: G Nat -> Type where
    GVector :: Vector a n -> GVector a ('G n)

data GPlusFree (size1 :: G Nat) (size2 :: G Nat) = GPlusFree
    { size1 :: GSing size1
    , size2 :: GSing size2
    , arr1 :: GVector Word8 size1
    , arr2 :: GVector Word8 size2
    , freeArr :: Vector Word8 4
    } deriving (GHC.Generic, Generic)

type family
    Tag2 (f :: G x -> G y -> Type) :: Type where
    Tag2 (f :: G x -> G y -> Type) = f ('Tag 0) ('Tag 1)
type family
    Rep2 (f :: G x -> G y -> Type) :: Type where
    Rep2 (f :: G x -> G y -> Type) = Rep (Tag2 f)
--data GSome2 f where
--    GSome2 :: Sing a -> Sing b -> f (G a) (G b) -> GSome2 f
data SomeRep2 (f :: G a -> G b -> Type) where
    SomeRep2 :: Sing a -> Sing b -> Rep (f ('G a) ('G b)) -> SomeRep2 f
-}

type family
    Lookup (i :: Nat) (xs :: [a]) :: a where
    Lookup 0 (a ': _ ) = a
    Lookup i (_ ': as) = Lookup (i-1) as
type family
    Update (i :: Nat) (a :: k) (xs :: [k]) :: [k] where
    Update 0 a (_ ': xs) = (a ': xs)
    Update i a (x ': xs) = x ': Update (i-1) a xs

lookupNP :: forall i ts. Sing i -> NP I ts -> Lookup i ts
lookupNP SNat (I a :* as) =
    ifZeroElse @i a (\(Proxy :: Proxy i1) -> unsafeCoerce $ lookupNP (sing @i1) as)
updateNP :: forall i ts a. Sing i -> a -> NP I ts -> NP I (Update i a ts)
updateNP SNat a (I x :* xs) =
    ifZeroElse @i (I a :* xs) (\(Proxy :: Proxy i1) -> unsafeCoerce $ I x :* updateNP (sing @i1) a xs)

--}--}--}--}--}--}

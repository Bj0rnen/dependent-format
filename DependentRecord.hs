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
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TemplateHaskell #-}

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

import Data.Proxy
import Data.Constraint
import Unsafe.Coerce
import Data.Constraint.Forall
import GHC.Types (Any)

import Data.Word
import Data.Bits
import Numeric.Natural

import Exinst

data Vector a n where
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

instance Serialize Word8 where
    serialize a = [a]
    deserialize (b : bs) = (b, bs)

instance KnownNat n => Serialize (Sing (n :: Nat)) where  -- 8-bit
    serialize SNat = [fromIntegral $ natVal @n Proxy]
    deserialize (n : bs)
        | fromIntegral n == natVal @n Proxy = (SNat, bs)
        | otherwise = error "Deserialized wrong SNat"

newtype Magic n = Magic (KnownNat n => Dict (KnownNat n))
magic :: forall n m o. (Natural -> Natural -> Natural) -> (KnownNat n, KnownNat m) :- KnownNat o
magic f = Sub $ unsafeCoerce (Magic Dict) (natVal (Proxy :: Proxy n) `f` natVal (Proxy :: Proxy m))
axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))
predecessor :: forall n n1. ((1 + n1) ~ n) :- ((n - 1) ~ n1)
predecessor = Sub axiom
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

instance (Serialize a, KnownNat n) => Serialize (Vector a n) where
    serialize (v :: Vector a n) =
        ifZeroElse @n [] $ \_ ->
            case v of
                x :> xs ->
                    serialize x ++ serialize xs \\ samePredecessor @n
    deserialize bs =
        ifZeroElse @n (Nil, bs) $ \(Proxy :: Proxy n1) ->
            case deserialize @a bs of
                (a, bs') ->
                    case deserialize @(Vector a n1) bs' of
                        (as, bs'') -> (a :> as, bs'')
instance Serialize a => Dict1 Serialize (Vector a) where
    dict1 SNat = Dict

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


slol = serialize lol
dlol :: (GHC.Rep1 DependentPair 2, [Word8])
dlol = deserialize [2, 1, 2]

lol' :: DependentPair 2
lol' = GHC.to1 (fst dlol)

instance Serialize (SomeSing Nat) where
    serialize (SomeSing (SNat :: Sing n)) = serialize (SNat @n)
    deserialize bs =
        case deserialize bs of
            (a :: Word8, bs') ->
                case someNatVal (fromIntegral a) of
                    SomeNat (Proxy :: Proxy n) ->
                        (SomeSing @Nat @n SNat, bs')

instance Serialize (Some1 DependentPair) where
    serialize (Some1 SNat (DependentPair SNat arr)) = serialize arr
    deserialize bs =
        case deserialize bs of
            (SomeSing (SNat :: Sing (size :: Nat)), bs') ->
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
instance Serialize a => Dict1 Serialize (GHC.K1 i a) where
    dict1 _ = Dict

instance Dict1 Serialize f => Dict1 Serialize (GHC.M1 s l f) where
    dict1 (s :: Sing a) = withDict (dict1 s :: Dict (Serialize (f a))) Dict
instance Dict1 Serialize f => Dict1 Serialize (GHC.Rec1 f) where
    dict1 (s :: Sing a) = withDict (dict1 s :: Dict (Serialize (f a))) Dict
instance (Dict1 Serialize f, Dict1 Serialize g) => Dict1 Serialize (f GHC.:*: g) where
    dict1 (s :: Sing a) =
        withDict (dict1 s :: Dict (Serialize (f a))) $
            withDict (dict1 s :: Dict (Serialize (g a))) $
                Dict
-- TODO: Can I write the non-Nat-specialized instance of the below, somehow?
instance Dict1 Serialize (Sing :: Nat -> Type) where
    dict1 SNat = Dict
instance Serialize (SomeSing t) => Serialize (Some1 (Sing :: t -> Type)) where
    serialize (Some1 s1 s2) = serialize (SomeSing s2)
    deserialize bs =
        case deserialize bs of
            (SomeSing s, bs') -> (Some1 s s, bs')

someLol :: Some1 (GHC.Rep1 DependentPair)
someLol = Some1 SNat $ GHC.from1 (DependentPair SNat (1 :> 2 :> Nil))
sdp = serialize someLol

data UseSizeTwice (size :: Nat) = UseSizeTwice
    { whatever :: Word8
    , size :: Sing size
    , arr1 :: Vector Word8 size
    , sizeAgain :: Sing size
    , arr2 :: Vector Word16 size
    , arr3 :: Vector Word8 size
    , sizeAgainAgain :: Sing size
    } deriving (GHC.Generic1)

instance Serialize Word16 where
    serialize a = [fromIntegral (a .&. 0xFF00) `shiftR` 8, fromIntegral (a .&. 0xFF)]
    deserialize bs =
        case deserialize bs of
            (a :> b :> Nil :: Vector Word8 2, bs') -> ((fromIntegral a) `shiftL` 8 .|. fromIntegral b, bs')

someUST :: Some1 (GHC.Rep1 UseSizeTwice)
someUST = Some1 SNat $ GHC.from1 $ UseSizeTwice 123 SNat (1 :> 2 :> 3 :> Nil) SNat (4 :> 5 :> 6 :> Nil) (7 :> 8 :> 9:> Nil) SNat
sust = serialize someUST

-- (Serialize (Some1 f)) means: We can deserialize an `f a` without knowing a, and doing so teaches us `a`'s value.
-- (Dict1 Serialize f) means: We can deserialize an `f a` given a (Dict (Serialize (f a))).
-- The way I see it, we need to somehow track where we know `a` and where we need to know `a`.
-- The deserialization is happening in order from first record field to last. We're allowed to make that assumption.
-- (:*:) is the most intriguing part, but even the simple ones like (M1) will appear at various stages.
-- Some of them will deserialize without knowing `a` and teach us a (Those that wrap a Sing).
-- Some will need to know `a` in order to deserialize. In this case of just one variable, these don't teach us more.
-- Some will deserialize fine with or without `a`, and won't teach us `a` if we don't know it.
-- For (:*:), the above cases apply in the outward-facing sense, but there's also interaction between the inner parts.
-- How

data DepLevel = Requiring | NonDep | Learning
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
type family
    DepLevelOf (f :: k -> Type) :: DepLevel where
    DepLevelOf (GHC.Rec0 _) = 'NonDep
    DepLevelOf (GHC.K1 _ _) = 'NonDep
    DepLevelOf Sing = 'Learning
    DepLevelOf (GHC.Rec1 f) = DepLevelOf f
    DepLevelOf (GHC.S1 _ f) = DepLevelOf f
    DepLevelOf (GHC.M1 _ _ f) = DepLevelOf f
    DepLevelOf (l GHC.:*: r) = ProductDepLevel (DepLevelOf l) (DepLevelOf r)
    DepLevelOf _ = 'Requiring
class (ldep ~ DepLevelOf l, rdep ~ DepLevelOf r) => Product1Serialize (ldep :: DepLevel) (rdep :: DepLevel) (l :: k -> Type) (r :: k -> Type) where
    p1serialize :: Some1 (l GHC.:*: r) -> [Word8]
    p1deserialize :: [Word8] -> (Some1 (l GHC.:*: r), [Word8])
instance
    ( 'Learning ~ DepLevelOf l
    , Serialize (Some1 l)
    , 'Requiring ~ DepLevelOf r
    , Dict1 Serialize r
    )
    => Product1Serialize 'Learning 'Requiring l r where
    p1serialize (Some1 (s :: Sing a) (a GHC.:*: b)) = serialize (Some1 s a) ++ (withDict (dict1 s :: Dict (Serialize (r a))) $ serialize b)
    p1deserialize bs =
        case deserialize bs of
            (Some1 (s :: Sing a) a, bs') ->
                case withDict (dict1 s :: Dict (Serialize (r a))) $ deserialize bs' of
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
    , ForallF Serialize l
    , 'Learning ~ DepLevelOf r
    , Serialize (Some1 r)
    )
    => Product1Serialize 'NonDep 'Learning (l :: t -> Type) r where
    p1serialize (Some1 (s :: Sing a) (a GHC.:*: b)) = (serialize a \\ instF @Serialize @l @a) ++ serialize (Some1 s b)
    p1deserialize bs =
        --withNothing $ \(Proxy :: Proxy (x :: t)) ->
        --    case deserialize bs \\ instF @Serialize @l @x of
        --        (a :: l x, bs') ->
        --            case deserialize bs' of
        --                (Some1 (s :: Sing a) (b :: r a), bs'') ->
        --                    let a' = unsafeCoerce a :: l a in  -- TODO: unsafeCoerce because I have no idea how to use instF for deserialization. I don't know if this safe usage at all.
        --                        (Some1 s (a' GHC.:*: b), bs'')
        --where
        --    withNothing :: forall r. (forall (x :: t). Proxy x -> r) -> r
        --    withNothing f = f Proxy
        case deserialize bs \\ instF @Serialize @l @Any of
            (a :: l Any, bs') ->
                case deserialize bs' of
                    (Some1 (s :: Sing a) (b :: r a), bs'') ->
                        (Some1 s (unsafeCoerce a GHC.:*: b), bs'')
--instF @c @f @x :: g x
instance
    ( 'Learning ~ DepLevelOf l
    , Serialize (Some1 l)
    , 'NonDep ~ DepLevelOf r
    , ForallF Serialize r
    )
    => Product1Serialize 'Learning 'NonDep (l :: t -> Type) r where
    p1serialize (Some1 (s :: Sing a) (a GHC.:*: b)) = serialize (Some1 s a) ++ (serialize b \\ instF @Serialize @r @a)
    p1deserialize bs =
        case deserialize bs of
            (Some1 (s :: Sing a) (a :: l a), bs') ->
                case deserialize bs' \\ instF @Serialize @r @a of
                    (b :: r a, bs'') ->
                        (Some1 s (a GHC.:*: b), bs'')

instance (Product1Serialize (DepLevelOf f) (DepLevelOf g) f g) => Serialize (Some1 (f GHC.:*: g)) where
    serialize a = p1serialize @_ @(DepLevelOf f) @(DepLevelOf g) a
    deserialize bs = p1deserialize @_ @(DepLevelOf f) @(DepLevelOf g) bs

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

instance Dict1 Show (Vector Word8) where
    dict1 _ = Dict

data Dependency a = NonDependent | Dependent a
    deriving Show

data instance Sing (d :: Dependency a) where
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
instance Dict2 Show DependentPlusFree where
    dict2 (SDependent SNat) (SDependent SNat) = Dict
    dict2 (SDependent SNat) SNonDependent = Dict
    dict2 SNonDependent (SDependent SNat) = Dict
    dict2 SNonDependent SNonDependent = Dict

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
            case s %~ sing @t @a of
                Proved Refl ->
                    Right s
                Disproved r ->
                    -- TODO: Can probably grap field name.
                    Left ("((Sing) Refuted: " ++ show a ++ " %~ " ++ show (demote @a) ++ ")")
instance (SingKind t, SDecide t, SingI (n :: t), Show (Demote t)) => GDepend' (a n) (Some1 a) where
    gdepend' (Some1 n a) =
        case n %~ sing @t @n of
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


data G a where
    G :: a -> G a
    Tag :: Nat -> G a

data GSing (a :: G t) where
    GSing :: Sing (a :: t) -> GSing ('G a)
data GVector a (n :: G Nat) where
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

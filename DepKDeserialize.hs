{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module DepKDeserialize where

import Vector
import DepState
import Knowledge
import Proof

import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.TypeLits
import Data.Kind

import GHC.TypeLits (TypeError(..), ErrorMessage(..), type (+))
import           Generics.Kind hiding (Nat, (:~:))

import Data.Constraint
import Data.Constraint.Unsafe
import Unsafe.Coerce

import Data.Word
import Data.Int
import Data.Bits
import Numeric.Natural

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Indexed.State
import Control.Monad.Indexed


data DepStateList :: Type -> Type where
    DZ :: DepStateList Type
    DS :: DepState -> DepStateList xs -> DepStateList (x -> xs)

data AtomList :: Type -> Type -> Type where
    AtomNil  :: AtomList d Type
    AtomCons :: Atom d k -> AtomList d ks -> AtomList d (k -> ks)

data KnowledgeList (ds :: DepStateList d) where
    KnowledgeNil :: KnowledgeList 'DZ
    KnowledgeCons
        :: Knowledge d (x :: k)
        -> KnowledgeList (ds :: DepStateList ks)
        -> KnowledgeList ('DS d ds :: DepStateList (k -> ks))


class RequireAtom (a :: Atom d k) (ds :: DepStateList d) where
    -- TODO: Make IxGet convenience function for this. And use everywhere.
    getAtom :: KnowledgeList ds -> SomeSing k
instance SingI a => RequireAtom ('Kon (a :: k)) ds where
    getAtom _ = SomeSing (sing @a)
instance RequireAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS 'Known ds) where
    getAtom (KnowledgeCons (KnowledgeK s) _) = SomeSing s
instance
    -- TODO: Any hope of showing the name of the type variable?
    --  With nested records, it might've gone by multiple names, I suppose...
    --  Still, if type variable names are accessible, we could in theory show some kind of stack trace.
    TypeError (Text "A type variable of kind '" :<>: ShowType k :<>: Text "' is required before it is known.") =>
    RequireAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS 'Unknown ds) where
    getAtom = error "unreachable"
instance RequireAtom ('Var v) ds => RequireAtom ('Var ('VS v) :: Atom (i -> ks) k) ('DS d ds) where
    getAtom (KnowledgeCons _ kl) = getAtom @ks @k @('Var v) @ds kl

type family
    LearnAtom (a :: Atom d k) (ds :: DepStateList d) :: DepStateList d where
    LearnAtom ('Kon _) ds = ds
    LearnAtom ('Var  'VZ   ) ('DS _ ds) = 'DS 'Known ds
    LearnAtom ('Var ('VS v)) ('DS d ds) = 'DS d (LearnAtom ('Var v) ds)
class LearnableAtom (a :: Atom d k) (ds :: DepStateList d) where  -- TODO: Bad name.
    -- TODO: `Maybe` to cover "contradiction". is an `Either` or something a better fit?
    -- TODO: Make IxGet convenience function for this. And use everywhere.
    learnAtom :: SomeSing k -> KnowledgeList ds -> Maybe (KnowledgeList (LearnAtom a ds))
instance (SingI a, SDecide k) => LearnableAtom ('Kon (a :: k)) ds where
    learnAtom (SomeSing s) kl =
        case s %~ sing @a of
            Proved Refl -> Just kl
            Disproved r -> Nothing
instance LearnableAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS 'Unknown ds) where
    learnAtom (SomeSing s) (KnowledgeCons KnowledgeU kl) = Just (KnowledgeCons (KnowledgeK s) kl)
instance SDecide k => LearnableAtom ('Var 'VZ :: Atom (k -> ks) k) ('DS 'Known ds) where
    learnAtom (SomeSing s) curr@(KnowledgeCons (KnowledgeK s') kl) =
        case s %~ s' of
            Proved Refl -> Just curr
            Disproved r -> Nothing
instance LearnableAtom ('Var v) ds => LearnableAtom ('Var ('VS v) :: Atom (i -> ks) k) ('DS d ds) where
    learnAtom ss (KnowledgeCons k kl) = KnowledgeCons k <$> learnAtom @ks @k @('Var v) @ds ss kl


-- TODO: Add meaningful structure.
data DeserializeError = DeserializeError String
    deriving (Show)

class IxMonad m => IxMonadError e m | m -> e where
    ithrowError :: e -> m i j a
instance MonadError e m => IxMonadError e (IxStateT m) where
    ithrowError e = IxStateT \_ -> throwError e
newtype IxGet (ds :: DepStateList d) (ds' :: DepStateList d) (a :: Type) =
    IxGet { runIxGet :: IxStateT (Either DeserializeError) (KnowledgeList ds, [Word8]) (KnowledgeList ds', [Word8]) a }
    deriving newtype (Functor)
deriving newtype instance Applicative (IxGet ds ds)
deriving newtype instance Monad (IxGet ds ds)
deriving newtype instance MonadError DeserializeError (IxGet ds ds)
-- TODO: Can I get an explanation for why I can't simply derive these?
-- TODO: Says it "cannot eta-reduce the representation type enough".
instance IxFunctor IxGet where
    imap f (IxGet a) = IxGet (imap f a)
instance IxPointed IxGet where
    ireturn a = IxGet (ireturn a)
instance IxApplicative IxGet where
    iap (IxGet f) (IxGet a) = IxGet (iap f a)
instance IxMonad IxGet where
    ibind f (IxGet a) = IxGet $ ibind (runIxGet . f) a
instance IxMonadError DeserializeError IxGet where
    ithrowError e = IxGet (ithrowError e)
getKnowledge :: IxGet ds ds (KnowledgeList ds)
getKnowledge = IxGet (fst <$> iget)
modifyKnowledge :: (KnowledgeList ds -> KnowledgeList ds') -> IxGet ds ds' ()
modifyKnowledge f = IxGet $ imodify \(kl, bs) -> (f kl, bs)
putKnowledge :: KnowledgeList ds' -> IxGet ds ds' ()
putKnowledge kl = modifyKnowledge (const kl)
getBytes :: IxGet ds ds [Word8]
getBytes = IxGet (snd <$> iget)
modifyBytes :: ([Word8] -> [Word8]) -> IxGet ds ds ()
modifyBytes f = IxGet $ imodify \(kl, bs) -> (kl, f bs)
putBytes :: [Word8] -> IxGet ds ds ()
putBytes bs = modifyBytes (const bs)
igetAtom
    :: forall (d :: Type) (k :: Type) (t :: Atom d k) (ds :: DepStateList d)
    .  RequireAtom t ds
    => IxGet ds ds (SomeSing k)
igetAtom = getKnowledge >>>= \kl -> ireturn $ getAtom @d @k @t @ds kl
-- TODO: Maybe this should take a DeserializeError. Or, right now, learnAtom
-- TODO: returns Maybe, but if it returned (Either LearningError), then
-- TODO: perhaps what we should take is a (LearningError -> DeserializeError).
-- TODO: The point is: "Learned something contradictory" is a very generic message.
ilearnAtom
    :: forall (d :: Type) (k :: Type) (t :: Atom d k) (ds :: DepStateList d)
    .  LearnableAtom t ds
    => SomeSing k -> IxGet ds (LearnAtom t ds) ()
ilearnAtom ss =
    getKnowledge >>>= \kl ->
    case learnAtom @d @k @t ss kl of
        Nothing -> ithrowError $ DeserializeError "Learned something contradictory"
        Just kl' -> putKnowledge kl'


data TheseK (f :: ks) (xs :: LoT ks) where
    TheseK :: Proxy xs -> f :@@: xs -> TheseK f xs
deriving instance Show (f :@@: xs) => Show (TheseK f xs)
-- TODO: This type is more of a workaround than an intentional design...
-- TODO: I struggle to even make a Show instance. Could I mitigate that by replacing (:@@:) and InterpretVars
-- TODO: with some concrete datatype(s)? Well AnyK is pretty much that type, so that logic is a bit circular...
-- TODO(2020-06-04): The above situation might be different, now that InterpretVars is gone.
data AnyK (f :: ks) where
    AnyK :: Proxy xs -> f :@@: xs -> AnyK f

class DepKDeserialize (f :: ks) where
    type Require (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint
    type Learn (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d
    depKSerialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks) (xs :: LoT ks)
        .  Require f as ds
        => Proxy as -> TheseK f xs -> IxState (KnowledgeList ds) (KnowledgeList (Learn f as ds)) [Word8]
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  Require f as ds
        -- TODO: Drop the proxy, if that's viable.
        => Proxy as -> IxGet ds (Learn f as ds) (AnyK f)

    -- TODO: I was going for a DerivingVia design rather than default signatures, but that had problems.
    type Require (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) = RequireK (RepK f) as ds
    type Learn (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) = LearnK (RepK f) as ds
    default depKSerialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks) (xs :: LoT ks)
        .  (GenericK f, DepKDeserializeK (RepK f), RequireK (RepK f) as ds, Learn f as ds ~ LearnK (RepK f) as ds)
        => Proxy as -> TheseK f xs -> IxState (KnowledgeList ds) (KnowledgeList (Learn f as ds)) [Word8]
    depKSerialize p (TheseK (Proxy :: Proxy xs) a) =
        depKSerializeK p (fromK @_ @f @xs a :: RepK f xs)
    default depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  (GenericK f, DepKDeserializeK (RepK f), RequireK (RepK f) as ds, Learn f as ds ~ LearnK (RepK f) as ds)
        => Proxy as -> IxGet ds (Learn f as ds) (AnyK f)
    depKDeserialize p =
        depKDeserializeK @_ @(RepK f) p >>>= \(AnyKK (r :: RepK f xs)) ->
        ireturn $ AnyK (Proxy @xs) (toK @_ @f @xs r)


class (DepKDeserialize a, Require a 'AtomNil 'DZ) => Serialize a
instance (DepKDeserialize a, Require a 'AtomNil 'DZ) => Serialize a
serialize :: forall a. Serialize a => a -> [Word8]
serialize a = fst $ runIxState (depKSerialize @Type @a @Type (Proxy @'AtomNil) (TheseK (Proxy @'LoT0) a)) KnowledgeNil
deserialize :: forall a. Serialize a => StateT [Word8] (Either DeserializeError) a
deserialize = 
    StateT $ \bs -> do
        (AnyK _ r, (_, bs')) <- runIxStateT (runIxGet $ depKDeserialize (Proxy @'AtomNil)) (KnowledgeNil, bs)
        return (r, bs')


-- Helpers for defining DepKDeserialize instances where there's already an instance with one less type variable applied.
-- Example: There's an instance for DepKDeserialize Foo; these helpers make it trivial to write a DepKDeserialize (Foo x) instance.
-- TODO: Can we make it even easier? DerivingVia?
depKSerialize1Up
    :: forall k ks (f :: k -> ks) (x :: k) d (ds :: DepStateList d) (as :: AtomList d ks) (xs :: LoT ks)
    . ( DepKDeserialize f
      , Learn (f x) as ds ~ Learn1Up (f x) as ds
      , Require (f x) as ds ~ Require1Up (f x) as ds
      , Require (f x) as ds
      )
    => Proxy as -> TheseK (f x) xs -> IxState (KnowledgeList ds) (KnowledgeList (Learn f ('AtomCons ('Kon x) as) ds)) [Word8]
depKSerialize1Up (Proxy :: Proxy as) (TheseK (Proxy :: Proxy xs) a) =
    depKSerialize @(k -> ks) @f (Proxy :: Proxy ('AtomCons ('Kon x) as)) (TheseK (Proxy :: Proxy (x :&&: xs)) a)
type family Require1Up (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint where
    Require1Up (f x) as ds = Require f ('AtomCons ('Kon x) as) ds
type family Learn1Up (f :: ks) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d where
    Learn1Up (f x) as ds = Learn f ('AtomCons ('Kon x) as) ds
depKDeserialize1Up
    :: forall k ks (f :: k -> ks) (x :: k) d (ds :: DepStateList d) (as :: AtomList d ks)
    . ( DepKDeserialize f
      , Learn (f x) as ds ~ Learn1Up (f x) as ds
      , Require (f x) as ds ~ Require1Up (f x) as ds
      , Require (f x) as ds
      )
    => Proxy as -> IxGet ds (Learn (f x) as ds) (AnyK (f x))
depKDeserialize1Up (Proxy :: Proxy as) =
    depKDeserialize @(k -> ks) @f (Proxy :: Proxy ('AtomCons ('Kon x) as)) >>>= \(AnyK (Proxy :: Proxy (xxs)) a) ->
    ireturn $ AnyK (Proxy :: Proxy (TailLoT xxs)) (unsafeCoerce a :: f x :@@: TailLoT xxs)  -- TODO: That's a kind of scary unsafeCoerce.


withoutKnowledge :: StateT [Word8] (Either DeserializeError) a -> IxGet ds ds a
withoutKnowledge (StateT f) =
    IxGet $ IxStateT \(kl, bs) -> do
        (a, bs') <- f bs
        return (a, (kl, bs'))

expectBytes :: [Word8] -> StateT [Word8] (Either DeserializeError) ()
expectBytes [] = return ()
expectBytes (b : bs) = do
    b' <- deserialize
    if b /= b' then
        throwError $ DeserializeError $
            "Wrong byte value was read. expected: " ++ show b ++ ", actual: " ++ show b'
    else do
        expectBytes bs

instance DepKDeserialize Word8 where
    type Require Word8 as ds = ()
    type Learn Word8 as ds = ds
    depKSerialize _ (TheseK _ a) = pure [a]
    depKDeserialize _ = AnyK Proxy <$> withoutKnowledge do
        bs <- get
        case bs of
            [] -> throwError $ DeserializeError "No more bytes to read!"
            (b : bs') -> do
                put bs'
                return b

instance DepKDeserialize Word16 where
    type Require Word16 as ds = ()
    type Learn Word16 as ds = ds
    depKSerialize _ (TheseK _ a) = pure
        [ fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    depKDeserialize _ = AnyK Proxy <$> withoutKnowledge do
        bs <- deserialize @(Vector Word8 2)
        case bs of
            a :> b :> Nil ->
                return
                    (       (fromIntegral a) `shiftL` 8
                        .|. fromIntegral b
                    )

instance DepKDeserialize Word32 where
    type Require Word32 as ds = ()
    type Learn Word32 as ds = ds
    depKSerialize _ (TheseK _ a) = pure
        [ fromIntegral ((a `shiftR` 24) .&. 0xFF)
        , fromIntegral ((a `shiftR` 16) .&. 0xFF)
        , fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    depKDeserialize _ = AnyK Proxy <$> withoutKnowledge do
        bs <- deserialize @(Vector Word8 4)
        case bs of
            a :> b :> c :> d :> Nil ->
                return
                    (       (fromIntegral a) `shiftL` 24
                        .|. (fromIntegral b) `shiftL` 16
                        .|. (fromIntegral c) `shiftL` 8
                        .|. fromIntegral d
                    )

instance DepKDeserialize Word64 where
    type Require Word64 as ds = ()
    type Learn Word64 as ds = ds
    depKSerialize _ (TheseK _ a) = pure
        [ fromIntegral ((a `shiftR` 56) .&. 0xFF)
        , fromIntegral ((a `shiftR` 48) .&. 0xFF)
        , fromIntegral ((a `shiftR` 40) .&. 0xFF)
        , fromIntegral ((a `shiftR` 32) .&. 0xFF)
        , fromIntegral ((a `shiftR` 24) .&. 0xFF)
        , fromIntegral ((a `shiftR` 16) .&. 0xFF)
        , fromIntegral ((a `shiftR` 8) .&. 0xFF)
        , fromIntegral (a .&. 0xFF)
        ]
    depKDeserialize _ = AnyK Proxy <$> withoutKnowledge do
        bs <- deserialize @(Vector Word8 8)
        case bs of
            a :> b :> c :> d :> e :> f :> g :> h :> Nil ->
                return
                    (       (fromIntegral a) `shiftL` 56
                        .|. (fromIntegral b) `shiftL` 48
                        .|. (fromIntegral c) `shiftL` 40
                        .|. (fromIntegral d) `shiftL` 32
                        .|. (fromIntegral e) `shiftL` 24
                        .|. (fromIntegral f) `shiftL` 16
                        .|. (fromIntegral g) `shiftL` 8
                        .|. fromIntegral h
                    )

instance DepKDeserialize Int8 where
    type Require Int8 as ds = ()
    type Learn Int8 as ds = ds
    depKSerialize _ (TheseK _ a) = pure [fromIntegral a]
    depKDeserialize _ = AnyK Proxy <$> withoutKnowledge do
        (bs :: [Word8]) <- get
        case bs of
            [] -> throwError $ DeserializeError "No more bytes to read!"
            (b : bs') -> do
                put bs'
                return $ fromIntegral b

-- TODO: This instance should go away.
instance DepKDeserialize Natural where  -- 8-bit
    type Require Natural as ds = ()
    type Learn Natural as ds = ds
    depKSerialize _ (TheseK _ a) = pure [fromIntegral a]
    depKDeserialize _ = AnyK Proxy <$> withoutKnowledge do
        b <- deserialize @Word8
        return $ fromIntegral b


-- TODO: Is it sensible that this is indexed by a TyVar and not a Nat?
type family
    AtomAt (n :: TyVar ks k) (as :: AtomList d ks) :: Atom d k where
    AtomAt 'VZ (AtomCons a _) = a
    AtomAt ('VS v) (AtomCons _ as) = AtomAt v as

instance (SingKind k, Serialize (Demote k)) => DepKDeserialize (WrappedSing :: k -> Type) where
    type Require (WrappedSing :: k -> Type) as ds = LearnableAtom (AtomAt 'VZ as) ds
    type Learn (WrappedSing :: k -> Type) as ds = LearnAtom (AtomAt 'VZ as) ds
    depKSerialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (k -> Type)) (xs :: LoT (k -> Type))
        .  Require (WrappedSing :: k -> Type) as ds
        => Proxy as -> TheseK (WrappedSing :: k -> Type) xs -> IxState (KnowledgeList ds) (KnowledgeList (Learn (WrappedSing :: k -> Type) as ds)) [Word8]
    depKSerialize _ (TheseK _ (WrapSing s)) =
        iget >>>= \kl ->
        case learnAtom @d @k @(AtomAt 'VZ as) (SomeSing s) kl of
            Nothing -> error "unreachable"
            Just kl' ->
                iput kl' >>>= \_ ->
                ireturn $ serialize @(Demote k) (FromSing s)
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (k -> Type))
        .  Require (WrappedSing :: k -> Type) as ds
        => Proxy as -> IxGet ds (Learn (WrappedSing :: k -> Type) as ds) (AnyK (WrappedSing :: k -> Type))
    depKDeserialize _ =
        getKnowledge >>>= \kl ->
        withoutKnowledge deserialize >>>= \(FromSing (s :: Sing (s :: k))) ->
        -- TODO: Would be awesome if we could show "expected" and "actual" in case of contradiction!
        ilearnAtom @d @k @(AtomAt 'VZ as) (SomeSing s) >>>= \_ ->
        ireturn $ AnyK (Proxy @(s :&&: 'LoT0)) (WrapSing s)

instance (SingKind k, Serialize (Demote k)) => DepKDeserialize (WrappedSing (a :: k)) where
    type Require (WrappedSing (a :: k)) as ds = Require1Up (WrappedSing (a :: k)) as ds
    type Learn (WrappedSing (a :: k)) as ds = Learn1Up (WrappedSing (a :: k)) as ds
    depKSerialize = depKSerialize1Up
    depKDeserialize = depKDeserialize1Up

instance DepKDeserialize Vector where
    type Require Vector as ds =
            ( DepKDeserialize (AtomKonConstructor (AtomAt 'VZ as))
            , Require (AtomKonConstructor (AtomAt 'VZ as)) (AtomKonAtomList (AtomAt 'VZ as)) ds
            , RequireAtom (AtomAt ('VS 'VZ) as) ds
            -- Saying that we don't learn from the elements might turn out to be overly strict.
            -- It wouldn't be hard to instead claim inside the methods that there's no harm in that.
            , Learn (AtomKonConstructor (AtomAt 'VZ as)) (AtomKonAtomList (AtomAt 'VZ as)) ds ~ ds
            )
    type Learn Vector as ds = ds
    depKSerialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Type -> Nat -> Type)) (xs :: LoT (Type -> Nat -> Type))
        .  Require Vector (as :: AtomList d (Type -> Nat -> Type)) ds
        => Proxy as -> TheseK Vector xs -> IxState (KnowledgeList ds) (KnowledgeList (Learn Vector as ds)) [Word8]
    depKSerialize (Proxy :: Proxy as) (TheseK (Proxy :: Proxy xs) v) =
        iget >>>= \kl ->
        case getAtom @d @Nat @(AtomAt ('VS 'VZ) as) kl of
            SomeSing (SNat :: Sing n) ->
                letT @(HeadLoT xs) \(Proxy :: Proxy a) ->
                axm @n @(InterpretVar ('VS 'VZ) xs) $
                matchVector v
                    (pure [])
                    \x (xs :: Vector a n1) ->
                        depKSerialize
                            @(AtomKonKind (AtomAt 'VZ as))
                            @(AtomKonConstructor (AtomAt 'VZ as))
                            (Proxy @(AtomKonAtomList (AtomAt 'VZ as)))
                            -- TODO: We probably only need to figure out the correct `xs` for
                            --  this TheseK to get rid of the unsafeCoerce. I guess it has to
                            --  be some type family that we apply to (AtomAt 'VZ as) and the
                            --  `xs` in scope.
                            (TheseK Proxy (unsafeCoerce x)) >>>= \bs1 ->
                        depKSerialize
                            @(Type -> Nat -> Type)
                            @Vector
                            (Proxy @('AtomCons (AtomAt 'VZ as) ('AtomCons ('Kon n1) 'AtomNil)))
                            (TheseK (Proxy @(a :&&: n1 :&&: 'LoT0)) xs) >>>= \bs2 ->
                        ireturn $ bs1 ++ bs2
    depKDeserialize
        :: forall d (ds :: DepStateList d) (as :: AtomList d (Type -> Nat -> Type))
        .  Require Vector (as :: AtomList d (Type -> Nat -> Type)) ds
        => Proxy as -> IxGet ds (Learn Vector as ds) (AnyK Vector)
    depKDeserialize (Proxy :: Proxy as) =
        -- This shouldn't have to be asserted. It's not like Learn would ever reduce knowledge.
        case unsafeCoerce (Refl @ds) ::
            ds :~: Learn (AtomKonConstructor (AtomAt 'VZ as)) (AtomKonAtomListStep (AtomAt 'VZ as) 'AtomNil) ds of
            Refl ->
                igetAtom @d @Nat @(AtomAt ('VS 'VZ) as) @ds >>>= \(SomeSing (SNat :: Sing n)) ->
                Vector.ifZeroElse @n
                    (return (AnyK (Proxy @(_ :&&: 0 :&&: 'LoT0)) Nil))
                    \(Proxy :: Proxy n1) ->
                        depKDeserialize
                            @(AtomKonKind (AtomAt 'VZ as))
                            @(AtomKonConstructor (AtomAt 'VZ as))
                            (Proxy @(AtomKonAtomList (AtomAt 'VZ as))) >>>= \(AnyK Proxy a) ->
                        depKDeserialize
                            @(Type -> Nat -> Type)
                            @Vector
                            (Proxy @('AtomCons (AtomAt 'VZ as) ('AtomCons ('Kon n1) 'AtomNil))) >>>= \(AnyK Proxy as) ->
                        return (AnyK Proxy (unsafeCoerce (a :> unsafeCoerce as)))

instance DepKDeserialize (Vector a) where
    type Require (Vector a) as ds = Require1Up (Vector a) as ds
    type Learn (Vector a) as ds = Learn1Up (Vector a) as ds
    depKSerialize = depKSerialize1Up
    depKDeserialize = depKDeserialize1Up

instance DepKDeserialize (Vector a n) where
    type Require (Vector a n) as ds = Require1Up (Vector a n) as ds
    type Learn (Vector a n) as ds = Learn1Up (Vector a n) as ds
    depKSerialize = depKSerialize1Up
    depKDeserialize = depKDeserialize1Up

data AnyKK :: (LoT ks -> Type) -> Type where
    AnyKK :: f xs -> AnyKK f

class DepKDeserializeK (f :: LoT ks -> Type) where
    type RequireK (f :: LoT ks -> Type) (as :: AtomList d ks) (ds :: DepStateList d) :: Constraint
    type LearnK (f :: LoT ks -> Type) (as :: AtomList d ks) (ds :: DepStateList d) :: DepStateList d
    depKSerializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks) (xs :: LoT ks)
        .  RequireK f as ds
        => Proxy as -> f xs -> IxState (KnowledgeList ds) (KnowledgeList (LearnK f as ds)) [Word8]
    depKDeserializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  RequireK f as ds
        => Proxy as -> IxGet ds (LearnK f as ds) (AnyKK f)

-- TODO: Write wappers around these where `t` is pinned to kind (Atom d Type)?
type family
    AtomKonKind (t :: Atom ks k) :: Type where
    AtomKonKind ('Kon (f :: k)) = k
    AtomKonKind (t :@: _) = AtomKonKind t
type family
    AtomKonKindT (t :: Atom ks Type) :: Type where
    AtomKonKindT t = AtomKonKind t

type family
    AtomKonConstructor (t :: Atom ks k) :: AtomKonKind t where
    AtomKonConstructor ('Kon (f :: k)) = f
    AtomKonConstructor (t :@: _) = AtomKonConstructor t
type family
    AtomKonConstructorT (t :: Atom ks Type) :: AtomKonKind t where
    AtomKonConstructorT t = AtomKonConstructor t

type family
    AtomKonAtomListStep (t :: Atom ks k) (as :: AtomList ks acc) :: AtomList ks (AtomKonKind t) where
    AtomKonAtomListStep ('Kon (f :: k)) as = as
    AtomKonAtomListStep (t :@: a) as = AtomKonAtomListStep t ('AtomCons a as)
type family
    AtomKonAtomList (t :: Atom ks k) :: AtomList ks (AtomKonKind t) where
    AtomKonAtomList t = AtomKonAtomListStep t 'AtomNil
type family
    AtomKonAtomListT (t :: Atom ks Type) :: AtomList ks (AtomKonKind t) where
    AtomKonAtomListT t = AtomKonAtomList t

-- TODO: Here be dragons. If this is actually part of a solution, I should better form an understanding around this part.
type family
    DereferenceAtom (base :: AtomList d ks) (a :: Atom ks k) :: Atom d k where
    DereferenceAtom _ ('Kon a) = 'Kon a
    DereferenceAtom as ('Var v) = AtomAt v as
    DereferenceAtom as (f :@: t) = DereferenceAtom as f :@: DereferenceAtom as t
type family
    DereferenceAtomList (base :: AtomList d ks) (as :: AtomList ks ks') :: AtomList d ks' where
    DereferenceAtomList _ 'AtomNil = 'AtomNil
    DereferenceAtomList base ('AtomCons a as) = 'AtomCons (DereferenceAtom base a) (DereferenceAtomList base as)

type family
    InterpretAll (as :: AtomList ks ks') (xs :: LoT ks) :: LoT ks' where
    InterpretAll 'AtomNil _ = 'LoT0
    InterpretAll ('AtomCons t as) xs = Interpret t xs :&&: InterpretAll as xs


instance (DepKDeserialize (AtomKonConstructor t)) => DepKDeserializeK (Field t) where
    type RequireK (Field t) as (ds :: DepStateList d) =
        Require (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds
    type LearnK (Field t) as (ds :: DepStateList d) =
        Learn (AtomKonConstructor t) (DereferenceAtomList as (AtomKonAtomList t)) ds
    depKSerializeK (Proxy :: Proxy as) (Field a :: Field t xs) =
        depKSerialize
        @(AtomKonKind t)
        @(AtomKonConstructor t)
        (Proxy @(DereferenceAtomList as (AtomKonAtomList t)))
        (TheseK (Proxy @(InterpretAll (AtomKonAtomList t) xs)) (unsafeCoerce a))
    depKDeserializeK (Proxy :: Proxy as) =
        depKDeserialize
            @(AtomKonKind t)
            @(AtomKonConstructor t)
            (Proxy @(DereferenceAtomList as (AtomKonAtomList t))) >>>= \(AnyK Proxy a) ->
        ireturn $ AnyKK (Field (unsafeCoerce a))

instance (DepKDeserializeK f, DepKDeserializeK g) => DepKDeserializeK (f :*: g :: LoT ks -> Type) where
    type RequireK (f :*: g) as ds =
        ( RequireK f as ds
        , RequireK g as (LearnK f as ds)
        )
    type LearnK (f :*: g) as ds = LearnK g as (LearnK f as ds)
    depKSerializeK p (a :*: b) =
        depKSerializeK p a >>>= \bs1 ->
        depKSerializeK p b >>>= \bs2 ->
        ireturn $ bs1 ++ bs2
    depKDeserializeK p =
        depKDeserializeK @_ @f p >>>= \(AnyKK a) ->
        depKDeserializeK @_ @g p >>>= \(AnyKK b) ->
        ireturn $ AnyKK (unsafeCoerce a :*: b)  -- TODO: Would be excellent to get rid of unsafeCoerce!

instance DepKDeserializeK f => DepKDeserializeK (M1 i c f) where
    type RequireK (M1 i c f) as ds = RequireK f as ds
    type LearnK (M1 i c f) as ds = LearnK f as ds
    depKSerializeK p (M1 a) = depKSerializeK p a
    depKDeserializeK p =
        depKDeserializeK @_ @f p >>>= \(AnyKK a) ->
        ireturn $ AnyKK (M1 a)

instance DepKDeserializeK U1 where
    type RequireK U1 as ds = ()
    type LearnK U1 as ds = ds
    depKSerializeK _ _ = pure []
    depKDeserializeK _ = ireturn $ AnyKK U1


type family
    IncrVar k (t :: Atom d a) :: Atom (k -> d) a where
    IncrVar _ ('Kon a) = 'Kon a
    IncrVar _ ('Var v) = 'Var ('VS v)
type family
    IncrVars k ks (as :: AtomList d ks) :: AtomList (k -> d) ks where
    IncrVars k Type 'AtomNil = 'AtomNil
    IncrVars k (k' -> ks) ('AtomCons t as) = 'AtomCons (IncrVar k t) (IncrVars k ks as)
type family
    IntroduceTyVar k ks (as :: AtomList d ks) :: AtomList (k -> d) (k -> ks) where
    IntroduceTyVar k ks as = 'AtomCons Var0 (IncrVars k ks as)
type family
    DiscardTyVar (ds :: DepStateList (k -> d)) :: DepStateList d where
    DiscardTyVar ('DS _ ds) = ds
instance DepKDeserializeK f => DepKDeserializeK (Exists k (f :: LoT (k -> ks) -> Type)) where
    type RequireK (Exists k (f :: LoT (k -> ks) -> Type)) as ds = RequireK f (IntroduceTyVar k ks as) ('DS 'Unknown ds)
    type LearnK (Exists k (f :: LoT (k -> ks) -> Type)) as ds = DiscardTyVar (LearnK f (IntroduceTyVar k ks as) ('DS 'Unknown ds))
    depKSerializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks) (xs :: LoT ks)
        .  RequireK (Exists k (f :: LoT (k -> ks) -> Type)) as ds
        => Proxy as -> (Exists k (f :: LoT (k -> ks) -> Type)) xs -> IxState (KnowledgeList ds) (KnowledgeList (LearnK (Exists k (f :: LoT (k -> ks) -> Type)) as ds)) [Word8]
    depKSerializeK _ (Exists (a :: f (x ':&&: xs))) =
        IxState $ \kl ->
            case runIxState
                        (depKSerializeK @_ @f (Proxy :: Proxy (IntroduceTyVar k ks as)) a)
                        (KnowledgeCons KnowledgeU kl) of
                (bs, KnowledgeCons _ kl') ->
                    (bs, kl')
    depKDeserializeK
        :: forall d (ds :: DepStateList d) (as :: AtomList d ks)
        .  RequireK (Exists k (f :: LoT (k -> ks) -> Type)) as ds
        => Proxy as -> IxGet ds (LearnK (Exists k (f :: LoT (k -> ks) -> Type)) as ds) (AnyKK (Exists k (f :: LoT (k -> ks) -> Type)))
    depKDeserializeK _ =
        IxGet $
            IxStateT $ \(kl, bs) ->
                case
                    runIxStateT
                        (runIxGet $ depKDeserializeK @_ @f (Proxy :: Proxy (IntroduceTyVar k ks as)))
                        (KnowledgeCons KnowledgeU kl, bs) of
                    Left e -> Left e
                    Right (AnyKK a, (KnowledgeCons _ kl', bs')) ->
                        Right (AnyKK (Exists (unsafeCoerce a)), (kl', bs'))

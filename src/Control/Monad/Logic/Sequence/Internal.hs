{-# LANGUAGE CPP #-}
#include "logict-sequence.h"
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}

#ifdef USE_PATTERN_SYNONYMS
{-# LANGUAGE PatternSynonyms #-}
#endif

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#endif

module Control.Monad.Logic.Sequence.Internal
(
#ifdef USE_PATTERN_SYNONYMS
    SeqT(MkSeqT, getSeqT, ..)
#else
    SeqT(..)
#endif
  , Seq
#ifdef USE_PATTERN_SYNONYMS
  , pattern MkSeq
  , getSeq
#endif
  , View(..)
  , Queue
  , MSeq(..)
  , AsUnitLoop(..)
  , toView
  , fromView
  , observeAllT
  , observeAll
  , observeT
  , observe
  , observeMaybeT
  , observeMaybe
)
where

import Control.Applicative
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Monad.Identity (Identity(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Logic.Class
import Control.Monad.IO.Class
import Data.SequenceClass hiding ((:<))
import qualified Data.SequenceClass as S
import Control.Monad.Logic.Sequence.Internal.Queue
import qualified Text.Read as TR

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid(..))
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup(..))
#endif

import qualified Data.Foldable as F
import GHC.Generics (Generic)


-- | Based on the LogicT improvements in the paper, Reflection without
-- Remorse. Code is based on the code provided in:
-- https://github.com/atzeus/reflectionwithoutremorse
--
-- Note: that code is provided under an MIT license, so we use that as
-- well.

data View m a = Empty | a :< SeqT m a
  deriving Generic

deriving instance (Show a, Show (SeqT m a)) => Show (View m a)
deriving instance (Read a, Read (SeqT m a)) => Read (View m a)
deriving instance (Eq a, Eq (SeqT m a)) => Eq (View m a)
deriving instance (Ord a, Ord (SeqT m a)) => Ord (View m a)
deriving instance Monad m => Functor (View m)

instance Monad m => Functor (View m) where
  fmap _ Empty = Empty
  fmap f (a :< s) = f a :< fmap f s

  _ <$ Empty = Empty
  x <$ (_ :< s) = x :< (x <$ s)

-- | An asymptotically efficient logic monad transformer. It is generally best to
-- think of this as being defined
--
-- @
-- newtype SeqT m a = 'MkSeqT' { 'getSeqT' :: m ('View' m a) }
-- @
--
-- Using the 'MkSeqT' pattern synonym with 'getSeqT', you can (almost) pretend
-- it's really defined this way! However, the real implementation is different,
-- so as to be more efficient in the face of deeply left-associated `<|>` or
-- `mplus` applications.
newtype SeqT m a = SeqT (Queue (m (View m a)))

#ifdef USE_PATTERN_SYNONYMS
pattern MkSeqT :: Monad m => m (View m a) -> SeqT m a
pattern MkSeqT{getSeqT} <- (toView -> getSeqT)
  where
    MkSeqT = fromView
{-# COMPLETE MkSeqT #-}

pattern MkSeq :: View Identity a -> Seq a
pattern MkSeq{getSeq} <- (runIdentity . toView -> getSeq)
  where
    MkSeq = fromView . Identity
{-# COMPLETE MkSeq #-}
#endif

-- | A specialization of 'SeqT' to the 'Identity' monad. You can
-- imagine that this is defined
--
-- @
-- newtype Seq a = MkSeq { getSeq :: View Identity a }
-- @
--
-- Using the 'MkSeq' pattern synonym with 'getSeq', you can pretend it's
-- really defined this way! However, the real implementation is different,
-- so as to be more efficient in the face of deeply left-associated `<|>`
-- or `mplus` applications.
type Seq = SeqT Identity

fromView :: m (View m a) -> SeqT m a
fromView = SeqT . singleton
{-# INLINE fromView #-}

toView :: Monad m => SeqT m a -> m (View m a)
toView (SeqT s) = case viewl s of
  EmptyL -> return Empty
  h S.:< t -> h >>= \x -> case x of
    Empty -> toView (SeqT t)
    hi :< SeqT ti -> return (hi :< SeqT (ti S.>< t))
{-# INLINEABLE toView #-}
{-# SPECIALIZE INLINE toView :: Seq a -> Identity (View Identity a) #-}

{-
Theorem: toView . fromView = id

Proof:

toView (fromView m)
=
toView (SeqT (singleton m))
=
case viewl (singleton m) of
    h S.:< t -> h >>= \x -> case x of
      Empty -> toView (SeqT t)
      hi :< SeqT ti -> return (hi :< SeqT (ti S.>< t))
=
m >>= \x -> case x of
  Empty -> toView (SeqT S.empty)
  hi :< SeqT ti -> return (hi :< SeqT ti)
=
m >>= \x -> case x of
  Empty -> return Empty
  hi :< SeqT ti -> return (hi :< SeqT ti)
= m
-}

instance (Show (m (View m a)), Monad m) => Show (SeqT m a) where
  showsPrec d s = showParen (d > app_prec) $
      showString "MkSeqT " . showsPrec (app_prec + 1) (toView s)
    where app_prec = 10

instance Read (m (View m a)) => Read (SeqT m a) where
  readPrec = TR.parens $ TR.prec app_prec $ do
      TR.Ident "MkSeqT" <- TR.lexP
      m <- TR.step TR.readPrec
      return (fromView m)
    where app_prec = 10

single :: Monad m => a -> m (View m a)
single a = return (a :< mzero)
{-# INLINE single #-}
{-# SPECIALIZE INLINE single :: a -> Identity (View Identity a) #-}

instance Monad m => Functor (SeqT m) where
  {-# INLINEABLE fmap #-}
  fmap f (SeqT q) = SeqT $ fmap (liftM (fmap f)) q
  {-# INLINABLE (<$) #-}
  x <$ SeqT q = SeqT $ fmap (liftM (x <$)) q

instance Monad m => Applicative (SeqT m) where
  {-# INLINE pure #-}
  {-# INLINABLE (<*>) #-}
  pure = fromView . single
  (<*>) = ap
  (*>) = (>>)
#if MIN_VERSION_base(4,10,0)
  liftA2 = liftM2
  {-# INLINABLE liftA2 #-}
#endif

instance Monad m => Alternative (SeqT m) where
  {-# INLINE empty #-}
  {-# INLINEABLE (<|>) #-}
  {-# SPECIALIZE INLINE (<|>) :: Seq a -> Seq a -> Seq a #-}
  empty = SeqT S.empty
  m <|> n = fromView (altView m n)

altView :: Monad m => SeqT m a -> SeqT m a -> m (View m a)
altView (toView -> m) n = m >>= \x -> case x of
  Empty -> toView n
  h :< t -> return (h :< cat t n)
    where cat (SeqT l) (SeqT r) = SeqT (l S.>< r)
{-# INLINE altView #-}

instance Monad m => Monad (SeqT m) where
  {-# INLINE return #-}
  {-# INLINEABLE (>>=) #-}
  {-# SPECIALIZE INLINE (>>=) :: Seq a -> (a -> Seq b) -> Seq b #-}
  return = fromView . single
  (toView -> m) >>= f = fromView $ m >>= \x -> case x of
    Empty -> return Empty
    h :< t -> f h `altView` (t >>= f)

  {-# INLINEABLE (>>) #-}
  (toView -> m) >> n = fromView $ m >>= \x -> case x of
    Empty -> return Empty
    _ :< t -> n `altView` (t >> n)

#if !MIN_VERSION_base(4,13,0)
  {-# INLINEABLE fail #-}
  fail = Fail.fail
#endif

instance Monad m => Fail.MonadFail (SeqT m) where
  {-# INLINEABLE fail #-}
  fail _ = SeqT S.empty

instance Monad m => MonadPlus (SeqT m) where
  {-# INLINE mzero #-}
  {-# INLINE mplus #-}
  mzero = Control.Applicative.empty
  mplus = (<|>)

#if MIN_VERSION_base(4,9,0)
instance Monad m => Semigroup (SeqT m a) where
  {-# INLINE (<>) #-}
  {-# INLINE sconcat #-}
  (<>) = mplus
  sconcat = foldr1 mplus
#endif

instance Monad m => Monoid (SeqT m a) where
  {-# INLINE mempty #-}
  {-# INLINE mappend #-}
  {-# INLINE mconcat #-}
  mempty = SeqT S.empty
  mappend = (<|>)
  mconcat = F.asum

instance MonadTrans SeqT where
  {-# INLINE lift #-}
  lift m = fromView (m >>= single)

instance Monad m => MonadLogic (SeqT m) where
  {-# INLINE msplit #-}
  {-# SPECIALIZE INLINE msplit :: Seq a -> Seq (Maybe (a, Seq a)) #-}
  msplit (toView -> m) = fromView $ do
    r <- m
    case r of
      Empty -> single Nothing
      a :< t -> single (Just (a, t))

observeAllT :: Monad m => SeqT m a -> m [a]
observeAllT (toView -> m) = m >>= go where
  go (a :< t) = liftM (a:) (toView t >>= go)
  go _ = return []
{-# INLINEABLE observeAllT #-}
{-# SPECIALIZE INLINE observeAllT :: Seq a -> Identity [a] #-}

#if !MIN_VERSION_base(4,13,0)
observeT :: Monad m => SeqT m a -> m a
#else
observeT :: MonadFail m => SeqT m a -> m a
#endif
observeT (toView -> m) = m >>= go where
  go (a :< _) = return a
  go Empty = fail "No results."
{-# INLINE observeT #-}

observe :: Seq a -> a
observe (toView -> m) = case runIdentity m of
  a :< _ -> a
  Empty -> error "No results."
{-# INLINE observe #-}

observeMaybeT :: Monad m => SeqT m (Maybe a) -> m (Maybe a)
observeMaybeT (toView -> m) = m >>= go where
  go (Just a :< _) = return (Just a)
  go (Nothing :< rest) = toView rest >>= go
  go Empty = return Nothing
{-# INLINEABLE observeMaybeT #-}

observeMaybe :: Seq (Maybe a) -> Maybe a
observeMaybe = runIdentity . observeMaybeT
{-# INLINE observeMaybe #-}

observeAll :: Seq a -> [a]
observeAll = runIdentity . observeAllT
{-# INLINE observeAll #-}

instance MonadIO m => MonadIO (SeqT m) where
  {-# INLINE liftIO #-}
  liftIO = lift . liftIO

{-# LANGUAGE CPP #-}
#include "logict-sequence.h"
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

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

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid(..))
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup(..))
#endif

import qualified Data.Foldable as F


-- | Based on the LogicT improvements in the paper, Reflection without
-- Remorse. Code is based on the code provided in:
-- https://github.com/atzeus/reflectionwithoutremorse
--
-- Note: that code is provided under an MIT license, so we use that as
-- well.

data View m a = Empty | a :< SeqT m a

-- | An asymptotically efficient logic monad transformer. It is generally best to
-- think of this as being defined
--
-- @
-- newtype SeqT m a = 'MkSeqT' { 'getSeqT' :: m ('View' m a) }
-- @
--
-- Using the 'MkSeqT' pattern synonym with 'getSeqT', you can (almost) pretend
-- it's really defined this way! However, the real implementation is different,
-- so as to be more efficient in the face of deeply nested monadic binds.
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
-- really defined this way!
type Seq = SeqT Identity

fromView :: m (View m a) -> SeqT m a
fromView = SeqT . singleton

toView :: Monad m => SeqT m a -> m (View m a)
toView (SeqT s) = case viewl s of
  EmptyL -> return Empty
  h S.:< t -> h >>= \x -> case x of
    Empty -> toView (SeqT t)
    hi :< SeqT ti -> return (hi :< SeqT (ti S.>< t))

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

single :: Monad m => a -> m (View m a)
single a = return (a :< mzero)

instance Monad m => Functor (SeqT m) where
  fmap f xs = xs >>= return . f

instance Monad m => Applicative (SeqT m) where
  pure = fromView . single
  (<*>) = liftM2 id

instance Monad m => Alternative (SeqT m) where
  empty = SeqT S.empty
  (toView -> m) <|> n = fromView (m >>= \x -> case x of
      Empty -> toView n
      h :< t -> return (h :< cat t n))
    where cat (SeqT l) (SeqT r) = SeqT (l S.>< r)

instance Monad m => Monad (SeqT m) where
  return = fromView . single
  (toView -> m) >>= f = fromView (m >>= \x -> case x of
    Empty -> return Empty
    h :< t -> toView (f h `mplus` (t >>= f)))
#if !MIN_VERSION_base(4,13,0)
  fail = Fail.fail
#endif

instance Monad m => Fail.MonadFail (SeqT m) where
  fail _ = SeqT S.empty

instance Monad m => MonadPlus (SeqT m) where
  mzero = Control.Applicative.empty
  mplus = (<|>)

#if MIN_VERSION_base(4,9,0)
instance Monad m => Semigroup (SeqT m a) where
  (<>) = mplus
  sconcat = foldr1 mplus
#endif

instance Monad m => Monoid (SeqT m a) where
  mempty = SeqT S.empty
  mappend = (<|>)
  mconcat = F.asum

instance MonadTrans SeqT where
  lift m = fromView (m >>= single)

instance Monad m => MonadLogic (SeqT m) where
  {-# INLINE msplit #-}
  msplit (toView -> m) = fromView $ do
    r <- m
    case r of
      Empty -> single Nothing
      a :< t -> single (Just (a, t))

observeAllT :: Monad m => SeqT m a -> m [a]
observeAllT (toView -> m) = m >>= go where
  go (a :< t) = liftM (a:) (observeAllT t)
  go _ = return []

#if !MIN_VERSION_base(4,13,0)
observeT :: Monad m => SeqT m a -> m a
#else
observeT :: MonadFail m => SeqT m a -> m a
#endif
observeT (toView -> m) = m >>= go where
  go (a :< _) = return a
  go Empty = fail "No results."

observe :: Seq a -> a
observe (toView -> m) = case runIdentity m of
  a :< _ -> a
  Empty -> error "No results."

observeMaybeT :: Monad m => SeqT m (Maybe a) -> m (Maybe a)
observeMaybeT (toView -> m) = m >>= go where
  go (Just a :< _) = return (Just a)
  go (Nothing :< rest) = toView rest >>= go
  go Empty = return Nothing

observeMaybe :: Seq (Maybe a) -> Maybe a
observeMaybe = runIdentity . observeMaybeT

observeAll :: Seq a -> [a]
observeAll = runIdentity . observeAllT

instance MonadIO m => MonadIO (SeqT m) where
  liftIO = lift . liftIO

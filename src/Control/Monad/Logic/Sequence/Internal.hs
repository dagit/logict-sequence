{-# LANGUAGE CPP #-}
#include "logict-sequence.h"
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

#ifdef USE_PATTERN_SYNONYMS
{-# LANGUAGE PatternSynonyms #-}
#endif

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Trustworthy #-}
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
-- so as to be more efficient in the face of deeply left-associated `<|>` or
-- `mplus` applications.
newtype SeqT m a = SeqT { runSeqT :: (Queue (m (View m a))) }

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
{-# INLINE CONLIKE [1] fromView #-}

toView :: Monad m => SeqT m a -> m (View m a)
toView (SeqT s) = case viewl s of
  EmptyL -> return Empty
  h S.:< t -> h >>= \x -> case x of
    Empty -> toView (SeqT t)
    hi :< SeqT ti -> return (hi :< SeqT (ti S.>< t))
{-# INLINEABLE[1] toView #-}

toViewIdentity :: Queue (Identity (View Identity a)) -> View Identity a
toViewIdentity s = go s
  where
    go x = case viewl x of
      EmptyL -> Empty
      (Identity Empty) S.:< t -> toViewIdentity t
      (Identity (hi :< SeqT ti)) S.:< t -> hi :< SeqT (ti S.>< t)
{-# INLINE[1] toViewIdentity #-}

{-# RULES
    "toView/fromView" forall m. fromView (toView m) = m;
    "toViewIdentity/fromView" [2] forall m. fromView (Identity (toViewIdentity m)) = SeqT m;
    "fromView/toView" forall m. toView (fromView m) = m;
    "toViewIdentity"  [3] toView = Identity . toViewIdentity . runSeqT;
  #-}


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
{-# INLINE CONLIKE single #-}
{-# SPECIALIZE INLINE single :: a -> Identity (View Identity a) #-}

instance Monad m => Functor (SeqT m) where
  {-# INLINEABLE fmap #-}
  fmap f xs = xs >>= return . f

instance Monad m => Applicative (SeqT m) where
  {-# INLINE CONLIKE pure #-}
  {-# INLINE (<*>) #-}
  pure = fromView . single
  (<*>) = liftM2 id

instance Monad m => Alternative (SeqT m) where
  {-# INLINE CONLIKE empty #-}
  {-# INLINEABLE (<|>) #-}
  empty = SeqT S.empty
  (<|>) = seqAlt

seqAlt :: Monad m => SeqT m a -> SeqT m a -> SeqT m a
seqAlt m n = fromView (toView m >>= \x -> case x of
  Empty -> toView n
  h :< t -> return (h :< SeqT (runSeqT t S.>< runSeqT n)))
{-# INLINE [2] seqAlt #-}

seqAltIdentity :: Seq a -> Seq a -> Seq a
seqAltIdentity m n = case toView m of
  Identity Empty -> n
  Identity (h :< t) -> fromView (Identity (h :< SeqT (runSeqT t S.>< runSeqT n)))
{-# INLINE[2] seqAltIdentity #-}

{-# RULES
      "seqAltIdentity" [3] seqAlt = seqAltIdentity;
  #-}


instance Monad m => Monad (SeqT m) where
  {-# INLINE CONLIKE return #-}
  {-# INLINEABLE (>>=) #-}
  return = fromView . single
  (>>=) = seqBind
#if !MIN_VERSION_base(4,13,0)
  {-# INLINEABLE fail #-}
  fail = Fail.fail
#endif

seqBind :: Monad m => SeqT m a -> (a -> SeqT m b) -> SeqT m b
seqBind a b = go a b
  where
  go m f = fromView (toView m >>= \x -> case x of
    Empty -> return Empty
    h :< t -> toView (f h `seqAlt` (t `go` f)))
{-# INLINEABLE [2] seqBind #-}

seqBindIdentity :: Seq a -> (a -> Seq b) -> Seq b
seqBindIdentity a b = go a b
  where
  go m f = case toView m of
    Identity Empty -> fromView (Identity Empty)
    Identity (h :< t) -> f h `seqAltIdentity` (t `go` f)
{-# INLINEABLE[2] seqBindIdentity #-}

{-# RULES
      "seqBindIdentity" [3] seqBind = seqBindIdentity;
  #-}

instance Monad m => Fail.MonadFail (SeqT m) where
  {-# INLINEABLE fail #-}
  fail _ = SeqT S.empty

instance Monad m => MonadPlus (SeqT m) where
  {-# INLINE CONLIKE mzero #-}
  {-# INLINE mplus #-}
  mzero = Control.Applicative.empty
  mplus = seqAlt

#if MIN_VERSION_base(4,9,0)
instance Monad m => Semigroup (SeqT m a) where
  {-# INLINE (<>) #-}
  {-# INLINE sconcat #-}
  (<>) = seqAlt
  sconcat = foldr1 seqAlt
#endif

instance Monad m => Monoid (SeqT m a) where
  {-# INLINE CONLIKE mempty #-}
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
  msplit = seqMsplit

seqMsplit :: Monad m => SeqT m a -> SeqT m (Maybe (a, SeqT m a))
seqMsplit (toView -> m) = fromView $ do
    r <- m
    case r of
      Empty -> single Nothing
      a :< t -> single (Just (a, t))
{-# INLINE[2] seqMsplit #-}

seqMsplitIdentity :: Seq a -> Seq (Maybe (a, Seq a))
seqMsplitIdentity m = fromView (case toView m of
  Identity Empty -> single Nothing
  Identity (a :< t) -> single (Just (a,t)))
{-# INLINE[2] seqMsplitIdentity #-}

{-# RULES
      "seqMsplitIdentity" [3] seqMsplit = seqMsplitIdentity;
  #-}

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

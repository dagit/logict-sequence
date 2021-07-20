{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#endif

module Control.Monad.Logic.Sequence
(   SeqT(..)
  , Seq
  , Queue
  , MSeq(..)
  , AsUnitLoop(..)
  , observeAllT
  , observeAll
  , observeT
  , observe
  , observeMaybeT
  , observeMaybe
  , module Control.Monad
  , module Control.Monad.Trans
)
where

import Control.Applicative
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Monad.Identity (Identity(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Trans as Trans
import Control.Monad.Logic.Class
import Control.Monad.IO.Class ()
import Data.TASequence.FastCatQueue as TA
import Data.SequenceClass as S

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid(..))
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup(..))
#endif

import qualified Data.Foldable as F
import qualified Data.Traversable as T


-- | Based on the LogicT improvements in the paper, Reflection without
-- Remorse. Code is based on the code provided in:
-- https://github.com/atzeus/reflectionwithoutremorse
--
-- Note: that code is provided under an MIT license, so we use that as
-- well.

type Queue = MSeq FastTCQueue

data AsUnitLoop a b c where
  UL :: !a -> AsUnitLoop a () ()

newtype MSeq s a = MSeq { getMS :: s (AsUnitLoop a) () () }

newtype SeqT m a = SeqT (Queue (m (Maybe (a, SeqT m a))))

type Seq a = SeqT Identity a

instance TASequence s => Sequence (MSeq s) where
  empty = MSeq tempty
  singleton = MSeq . tsingleton . UL
  l >< r = MSeq (getMS l TA.>< getMS r)
  l |> x = MSeq (getMS l TA.|> UL x)
  x <| r = MSeq (UL x TA.<| getMS r)
  viewl s = case tviewl (getMS s) of
    TAEmptyL -> EmptyL
    UL h TA.:< t -> h S.:< MSeq t
  viewr s = case tviewr (getMS s) of
    TAEmptyR -> EmptyR
    p TA.:> UL l -> MSeq p S.:> l

instance TASequence s => Functor (MSeq s) where
  fmap f = go where
    go q = case viewl q of
      EmptyL -> S.empty
      h S.:< t -> f h S.<| go t

instance TASequence s => F.Foldable (MSeq s) where
  foldMap f = fm where
    fm q = case viewl q of
      EmptyL -> mempty
      h S.:< t -> f h `mappend` fm t

instance TASequence s => T.Traversable (MSeq s) where
  sequenceA q = case viewl q of
    EmptyL -> pure S.empty
    h S.:< t -> pure (S.<|) <*> h <*> T.sequenceA t

fromView :: m (Maybe (a, SeqT m a)) -> SeqT m a
fromView = SeqT . singleton

toView :: Monad m => SeqT m a -> m (Maybe (a, SeqT m a))
toView (SeqT s) = case viewl s of
  EmptyL -> return Nothing
  h S.:< t -> h >>= \x -> case x of
    Nothing -> toView (SeqT t)
    Just (hi, SeqT ti) -> return (Just (hi, SeqT (ti S.>< t)))

single :: (MonadPlus mp, Monad m) => a -> m (Maybe (a, mp b))
single a = return (Just (a, mzero))

instance Monad m => Functor (SeqT m) where
  fmap f xs = xs >>= return . f

instance Monad m => Applicative (SeqT m) where
  pure = fromView . single
  (<*>) = liftM2 id

instance Monad m => Alternative (SeqT m) where
  empty = SeqT (MSeq tempty)
  (toView -> m) <|> n = fromView (m >>= \x -> case x of
      Nothing -> toView n
      Just (h,t) -> return (Just (h, cat t n)))
    where cat (SeqT l) (SeqT r) = SeqT (l S.>< r)

instance Monad m => Monad (SeqT m) where
  return = fromView . single
  (toView -> m) >>= f = fromView (m >>= \x -> case x of
    Nothing -> return Nothing
    Just (h,t) -> toView (f h `mplus` (t >>= f)))
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
  mempty = SeqT (MSeq tempty)
  mappend = (<|>)
  mconcat = F.asum

instance MonadTrans SeqT where
  lift m = fromView (m >>= single)

instance Monad m => MonadLogic (SeqT m) where
  msplit (toView -> m) = lift m

observeAllT :: Monad m => SeqT m a -> m [a]
observeAllT (toView -> m) = m >>= go where
  go (Just (a,t)) = liftM (a:) (observeAllT t)
  go _ = return []

#if !MIN_VERSION_base(4,13,0)
observeT :: Monad m => SeqT m a -> m a
#else
observeT :: MonadFail m => SeqT m a -> m a
#endif
observeT (toView -> m) = m >>= go where
  go (Just (a, _)) = return a
  go _ = fail "No results."

observe :: Seq a -> a
observe (toView -> m) = case runIdentity m of
  Just (a, _) -> a
  _ -> error "No results."

observeMaybeT :: Monad m => SeqT m (Maybe a) -> m (Maybe a)
observeMaybeT (toView -> m) = m >>= go where
  go (Just (Just a, _)) = return (Just a)
  go _ = return Nothing

observeMaybe :: Seq (Maybe a) -> Maybe a
observeMaybe = runIdentity . observeMaybeT

observeAll :: Seq a -> [a]
observeAll = runIdentity . observeAllT

instance MonadIO m => MonadIO (SeqT m) where
  liftIO = lift . liftIO

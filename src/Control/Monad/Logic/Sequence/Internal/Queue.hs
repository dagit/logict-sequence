{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#endif

module Control.Monad.Logic.Sequence.Internal.Queue
(  Queue
  , MSeq(..)
  , AsUnitLoop(..)
)
where

import Data.TASequence.FastCatQueue hiding ((:<))
import qualified Data.TASequence.FastCatQueue as TA
import Data.SequenceClass hiding ((:<))
import qualified Data.SequenceClass as S

import Control.Monad.Logic.Sequence.Internal.AsUnitLoop (AsUnitLoop (..))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid(..))
#endif

#if MIN_VERSION_base(4,9,0) && !MIN_VERSION_base(4,11,0)
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

newtype MSeq s a = MSeq { getMS :: s (AsUnitLoop a) () () }

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

#if MIN_VERSION_base(4,9,0)
instance TASequence s => Semigroup (MSeq s a) where
  (<>) = (S.><)
#endif

instance TASequence s => Monoid (MSeq s a) where
  mempty = S.empty
#if MIN_VERSION_base(4,9,0)
  mappend = (<>)
#else
  mappend = (S.><)
#endif

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

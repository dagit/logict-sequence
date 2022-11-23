{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveTraversable #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
#endif
{-# LANGUAGE Safe #-}

module Control.Monad.Logic.Sequence.Internal.Queue
(  Queue
)
where

import Data.SequenceClass hiding ((:<))
import qualified Data.SequenceClass as S

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
import qualified Control.Monad.Logic.Sequence.Internal.ScheduledQueue as SQ


-- | Based on the LogicT improvements in the paper, Reflection without
-- Remorse. Code is based on the code provided in:
-- https://github.com/atzeus/reflectionwithoutremorse
--
-- Note: that code is provided under an MIT license, so we use that as
-- well.

data Queue a
  = Empty
  | a :< SQ.Queue (Queue a)
  deriving (Functor, F.Foldable, T.Traversable)

instance Sequence Queue where
  {-# INLINE empty #-}
  empty = Empty
  {-# INLINE singleton #-}
  singleton a = a :< S.empty
  {-# INLINE (><) #-}
  Empty >< r = r
  (a :< q) >< r = a :< (q |> r)
  {-# INLINE (|>) #-}
  l |> x = l >< singleton x
  {-# INLINE (<|) #-}
  x <| r = singleton x >< r
  {-# INLINE viewl #-}
  viewl Empty     = EmptyL
  viewl (t :< q0) = t S.:< linkAll q0
    where
    linkAll :: SQ.Queue (Queue a) -> Queue a
    linkAll v = case viewl v of
      EmptyL -> Empty
      Empty S.:< t' -> linkAll t'
      (x :< q) S.:< t' -> x :< (q |> linkAll t')

#if MIN_VERSION_base(4,9,0)
instance Semigroup (Queue a) where
  {-# INLINE (<>) #-}
  (<>) = (S.><)
#endif

instance Monoid (Queue a) where
  {-# INLINE mempty #-}
  mempty = S.empty
  {-# INLINE mappend #-}
#if MIN_VERSION_base(4,9,0)
  mappend = (<>)
#else
  mappend = (S.><)
#endif

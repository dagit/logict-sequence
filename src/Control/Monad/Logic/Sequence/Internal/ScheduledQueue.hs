{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}


-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Logic.Sequence.Internal.ScheduledQueue
-- Copyright   :  (c) Atze van der Ploeg 2014
--                (c) David Feuer 2021
-- License     :  BSD-style
-- Maintainer  :  David.Feuer@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- A sequence, a queue, with worst case constant time: '|>', and 'viewl'.
--
-- Based on: "Simple and Efficient Purely Functional Queues and Deques", Chris Okasaki,
-- Journal of Functional Programming 1995
--
-----------------------------------------------------------------------------

module Control.Monad.Logic.Sequence.Internal.ScheduledQueue
  ( Queue
  ) where
import Data.SequenceClass (Sequence, ViewL (..))
import qualified Data.SequenceClass as S
import Data.Foldable
import qualified Data.Traversable as T
import qualified Control.Applicative as A

#if !MIN_VERSION_base(4,8,0)
import Data.Functor (Functor (..))
import Data.Monoid (Monoid (..))
#endif

infixl 5 :>
-- | A strict-spined snoc-list
data SL a
  = SNil
  | !(SL a) :> a
  deriving Functor

-- | Append a snoc list to a list.
--
-- Precondition: |f| = |r| - 1
appendSL :: [a] -> SL a -> [a]
appendSL f r = rotate f r []

-- Precondition:
-- |f| = |r| - 1
rotate :: [a] -> SL a -> [a] -> [a]
rotate [] (_SNil :> y) a = y : a
rotate (x : f) (r :> y) a = x : rotate f r (y : a)
rotate _f _a _r  = error "Invariant |f| = |r| + |a| - 1 broken"

-- | A scheduled banker's queue, as described by Okasaki. In theory, we only
-- need a queue supporting constant /amortized/ time operations. In practice,
-- once a queue gets large, linear-time pauses and cache effects relating to
-- rebuilding start to hurt.
data Queue a =
  RQ ![a]    -- front (f)
     !(SL a) -- rear (r)
     ![a]  -- schedule (a)
-- Invariant: |f| = |r| + |a|
  deriving Functor
  -- We would much rather write
  --
  --   data Queue a = forall x. RQ ![a] !(SL a) ![x]
  --
  -- to guarantee we don't accidentally look at elements in the schedule.
  -- Unfortuately, GHC can't currently unpack types with existentials, and
  -- we want to unpack into the catenable queue constructor. We used to use
  -- [Any], but the modern unsafeCoerce makes that produce rather messy core,
  -- and I'm a bit concerned about the term sizes for inlining and such.

queue :: [a] -> SL a -> [a] -> Queue a
-- precondition : |f| = |r| + |a| - 1
-- postcondition: |f| = |r| + |a|
queue f r [] =
  let
    f' = appendSL f r
    -- We NOINLINE f' to make sure that walking the schedule actually forces
    -- the front of the queue. GHC probably won't duplicate appendSL anyway,
    -- but let's be sure.
    {-# NOINLINE f' #-}
  in RQ f' SNil f'
queue f r (_h : t) = RQ f r t

instance Sequence Queue where
  empty = RQ [] SNil []
  singleton x =
    let
      c = [x]
    in RQ c SNil c
  -- The special case for [] gives us better optimizations
  -- for singleton catenable queues.
  RQ [] _ _ |> x = S.singleton x
  RQ f r a |> x = queue f (r :> x) a

  viewl (RQ [] _SNil _nil) = EmptyL
  viewl (RQ (h : t) f a) = h :< queue t f a

instance Foldable Queue where
  foldr c n = \q -> go q
    where
      go q = case S.viewl q of
        EmptyL -> n
        h :< t -> c h (go t)
  foldl' f b0 = \q -> go q b0
    where
      go q !b = case S.viewl q of
        EmptyL -> b
        h :< t -> go t (f b h)
#if MIN_VERSION_base(4,8,0)
  null (RQ [] _SNil _nil) = True
  null _ = False

  -- Invariant: |f| = |r| + |a|. The length of the queue is
  -- |f| + |r|
  -- We can calculate that as either 2 * |r| + |a|
  -- or 2 * |f| - a. I suspect the latter will give better
  -- cache utilization.
  length (RQ f _ a) = 2 * length f - length a
#endif

instance T.Traversable Queue where
  traverse f = fmap fromList . go
    where
      go q = case S.viewl q of
        EmptyL -> A.pure []
        h :< t -> A.liftA2 (:) (f h) (go t)

fromList :: [a] -> Queue a
fromList f = RQ f SNil f

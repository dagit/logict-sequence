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
  (Queue) where
import Data.SequenceClass hiding ((:>))
import Data.Foldable
import qualified Data.Traversable as T
import Control.Monad.Logic.Sequence.Internal.Any
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
rotate [] (~SNil :> y) a = y : a
rotate (x : f) (r :> y) a = x : rotate f r (y : a)
rotate _f _a _r  = error "Invariant |f| = |r| + |a| - 1 broken"

-- | A scheduled Banker's Queue, as described by Okasaki.
data Queue a = RQ ![a] !(SL a) ![Any]
-- Invariant: |f| = |r| + |a|
  deriving Functor
  -- We use 'Any' rather than an existential to allow GHC to unpack
  -- queues. In particular, we want to unpack into the catenable queue
  -- constructor.

queue :: [a] -> SL a -> [Any] -> Queue a
-- precondition : |f| = |r| + |a| - 1
-- postcondition: |f| = |r| + |a|
queue f r [] =
  let
    f' = appendSL f r
    {-# NOINLINE f' #-}
  in RQ f' SNil (toAnyList f')
queue f r (_h : t) = RQ f r t

instance Sequence Queue where
  empty = RQ [] SNil []
  singleton x =
    let
      c = [x]
      {-# NOINLINE c #-}
    in RQ c SNil (toAnyList c)
  RQ f r a |> x = queue f (r :> x) a

  viewl (RQ [] ~SNil ~[]) = EmptyL
  viewl (RQ (h : t) f a) = h :< queue t f a

instance Foldable Queue where
  foldr c n = \q -> go q
    where
      go q = case viewl q of
        EmptyL -> n
        h :< t -> c h (go t)
#if MIN_VERSION_base(4,6,0)
  foldl' f b0 = \q -> go q b0
    where
      go q !b = case viewl q of
        EmptyL -> b
        h :< t -> go t (f b h)
#endif

instance T.Traversable Queue where
  traverse f = fmap fromList . go
    where
      go q = case viewl q of
        EmptyL -> A.pure []
        h :< t -> A.liftA2 (:) (f h) (go t)

fromList :: [a] -> Queue a
fromList = foldl' (|>) empty

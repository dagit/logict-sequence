{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveTraversable #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
#endif
{-# LANGUAGE Trustworthy #-} -- for rules

-- | Based on the LogicT improvements in the paper, Reflection without
-- Remorse. Code is based on the code provided in:
-- https://github.com/atzeus/reflectionwithoutremorse
--
-- Note: that code is provided under an MIT license, so we use that as
-- well.
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
import Data.Coerce (coerce)

-- | A peculiarly lazy catenable queue. Note that appending multiple
-- 'empty' queues to a non-empty queue can break the amortized constant
-- bound for 'viewl' in the persistent case.
--
-- Contextual note: We could actually make these *non-empty* catenable
-- queues, in which case the wonkiness around appending @empty@ would go
-- away. In 'Control.Monad.Logic.Sequence.Internal.SeqT', @SeqT Empty@ is
-- really just an optimized representation of
--
--   @SeqT (singleton (pure Empty))@
--
-- where the @Empty@ in the latter is an empty @ViewT@.
data Queue a
  = Empty
  | a :< SQ.Queue (Queue a)
  deriving (F.Foldable, T.Traversable)

instance Functor Queue where
  fmap f q = mapQueue f q

mapQueue :: (a -> b) -> Queue a -> Queue b
mapQueue _f Empty = Empty
mapQueue f (a :< q) = f a :< fmap (mapQueue f) q
{-# NOINLINE [1] mapQueue #-}

-- These rules aren't (currently) used for SeqT operations, but they're
-- legitimate.
{-# RULES
"fmap/fmap" forall f g q. mapQueue f (mapQueue g q) = mapQueue (f . g) q
"fmap/coerce" mapQueue coerce = coerce
 #-}

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

-- We pull this out of viewl because we don't want to inline it
-- at every viewl call site.
linkAll :: SQ.Queue (Queue a) -> Queue a
linkAll v = case viewl v of
  EmptyL -> Empty
  Empty S.:< v' -> linkAll v'
  (x :< q) S.:< v' -> x :<
    -- We check if v' is empty to avoid *unnecessarily* inserting empty
    -- queues. We're allowed to force v' here, because it came from viewing
    -- v; it's not been suspended lazily.
    case viewl v' of
      EmptyL -> q
      _ -> q |> linkAll v'

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

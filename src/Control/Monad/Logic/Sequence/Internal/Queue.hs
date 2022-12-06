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
  | a :< {-# UNPACK #-} !(SQ.Queue (Queue a))
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
  {-# INLINABLE (><) #-}
  p >< q = p `append` q
  {-# INLINABLE (|>) #-}
  l |> x = l >< singleton x
  {-# INLINABLE (<|) #-}
  x <| r = x :< singleton r
  {-# INLINE viewl #-}
  viewl Empty     = EmptyL
  viewl (x :< q0)  = x S.:< linkAll q0

linkAll :: SQ.Queue (Queue a) -> Queue a
linkAll q = case viewl q of
    EmptyL -> Empty
    t S.:< q'  -> linkAll' t q'

linkAll' :: Queue a -> SQ.Queue (Queue a) -> Queue a
linkAll' Empty q' = linkAll q'
linkAll' t@(y :< q) q' = case viewl q' of
  EmptyL -> t
  -- Note: h could potentially be _|_, but that's okay because we don't force
  -- the recursive call.
  h S.:< t' -> y :< (q |> linkAll' h t')

-- I experimented with writing RULES for append, but (short of an explicit
-- staged INLINE) I couldn't do so while getting it to inline into <| when the
-- latter was defined x <| r = singleton x >< r. That made me a bit nervous
-- about other situations it might not inline, so I gave up on those. It's
-- unfortunate, because it seems likely that appends are (slightly) better
-- associated to the left or to the right (I haven't checked which), and it
-- would be nice to reassociate them whichever way is better.
append :: Queue a -> Queue a -> Queue a
append Empty r = r
append (a :< q) r = a :< (q |> r)

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

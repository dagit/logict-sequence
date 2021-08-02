{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs, ViewPatterns, TypeOperators #-}


-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Sequence.FastQueue
-- Copyright   :  (c) Atze van der Ploeg 2014
-- License     :  BSD-style
-- Maintainer  :  atzeus@gmail.org
-- Stability   :  provisional
-- Portability :  portable
--
-- A sequence, a queue, with worst case constant time: '|>', and 'tviewl'.
--
-- Based on: "Simple and Efficient Purely Functional Queues and Deques", Chris Okasaki,
-- Journal of Functional Programming 1995
--
-----------------------------------------------------------------------------

module Control.Monad.Logic.Sequence.Internal.QueueCopy
  (Queue) where
import Control.Applicative.Backwards
import Data.SequenceClass
import Data.Foldable
import Data.Traversable
import Control.Monad.Logic.Sequence.Internal.Any
import Prelude hiding (foldr,foldl)

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (pure, (<$>), (<*>))
import Data.Functor (Functor (..))
import Data.Monoid (Monoid (..))
#endif

revAppend :: [a] -> [a] -> [a]
revAppend l r = rotate l r []
-- precondtion : |a| = |f| - (|r| - 1)
-- postcondition: |a| = |f| - |r|
rotate :: [a] -> [a] -> [a] -> [a]
rotate [] [] r = r
rotate [] [y] r = y : r
rotate (x : f) (y : r) a = x : rotate f r (y : a)
rotate _f _a _r  = error "Invariant |a| = |f| - (|r| - 1) broken"

-- | A scheduled Banker's Queue, as described by Okasaki.
data Queue a where
  -- We use 'Any' rather than an existential to allow GHC to unpack
  -- queues if it's so inclined.
  RQ :: ![a] -> ![a] -> ![Any] -> Queue a

queue :: [a] -> [a] -> [Any] -> Queue a
queue f r [] = let f' = revAppend f r 
                 in RQ f' [] (toAnyList f')
queue f r (_h : t) = RQ f r t

instance Functor Queue where
  fmap phi (RQ f r a) = RQ (fmap phi f) (fmap phi r) (toAnyList a)
  x <$ (RQ f r a) = RQ (x <$ f) (x <$ r) (toAnyList a)

instance Foldable Queue where
  foldMap phi (RQ f r _a) = foldMap phi f `mappend` foldMap phi (Backwards r)
  foldl f = loop where
    loop i s = case viewl s of
          EmptyL -> i
          h :< t -> loop (f i h) t
  foldr f i = \s -> foldr f i (reverse $ toRevList s)
    where toRevList s = case viewl s of
           EmptyL -> []
           h :< t -> h : toRevList t

instance Sequence Queue where
 empty = RQ [] [] []
 singleton x = let c = [x] in queue c [] (toAnyList c)
 RQ f r a |> x = queue f (x : r) a

 viewl (RQ [] ~[] ~[]) = EmptyL
 viewl (RQ (h : t) f a) = h :< queue t f a

instance Traversable Queue where
  sequenceA q = case viewl q of
     EmptyL -> pure empty
     h :< t  -> (<|) <$> h <*> sequenceA t

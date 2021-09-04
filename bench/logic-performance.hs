-------------------------------------------------------------------------
-- |
-- Copyright   : (c) 2016-2021 Koji Miyazato,
--               (c) 2021 Jason Dagit
-- License     : MIT
--
-- Port of a benchmark script by its author, originally written for
-- <https://gitlab.com/viercc/ListT>
-- 
-- Performance Tests on various MonadLogic implementations.
-- (1) []
-- (2) Data.Sequence.Seq
-- (3) ListT m
-- (4) LogicT m
-- (5) SeqT m
-------------------------------------------------------------------------

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main(main) where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Identity
import Control.Monad.ST
import qualified Data.Foldable as F
import Data.Monoid (Alt (..))
import Data.Tree ( Tree(..) )

import Control.Monad.Logic (MonadLogic (..))
import qualified Control.Monad.Logic as Orig
import qualified Control.Monad.Logic.Sequence as L
import Data.Sequence (Seq, ViewL (..))
import qualified Data.Sequence as Seq
import ListT

import Gauge.Main
------------------------------------------------------------------------
-- Orphan instances

-- make Seq an instance of MonadLogic using viewl
instance MonadLogic Seq where
  msplit s = case Seq.viewl s of
    EmptyL -> return Nothing
    a :< as -> return (Just (a, as))

instance Monad m => MonadLogic (ListT m) where
  msplit = lift . uncons
  interleave as bs = ListT $ uncons as >>= \case
    Nothing -> uncons bs
    Just (a,as') -> pure (Just (a, interleave bs as'))

------------------------------------------------------------------------
-- how to run MonadLogic instances

-- | [a].
runList :: [a] -> [a]
runList = id
{-# INLINABLE runList #-}

-- | ListT. Most basic Backtracking monad.
runListT_I :: ListT Identity a -> [a]
runListT_I = runIdentity . toList
{-# INLINABLE runListT_I #-}

-- | ListT ST.
runListT_S :: (forall s. ListT (ST s) a) -> [a]
runListT_S ma = runST (toList ma)
{-# INLINABLE runListT_S #-}

-- | Seq. Asymptotically fast but constants are large. No transformer version.
runContainersSeq :: Seq a -> [a]
runContainersSeq = F.toList
{-# INLINABLE runContainersSeq #-}

-- | Logic. Very fast Monad/MonadPlus operation. Slow interleave.
runLogicT_I :: Orig.Logic a -> [a]
runLogicT_I = Orig.observeAll
{-# INLINABLE runLogicT_I #-}

runLogicT_S :: (forall s. Orig.LogicT (ST s) a) -> [a]
runLogicT_S ma = runST (Orig.observeAllT ma)
{-# INLINABLE runLogicT_S #-}

-- | SeqT from logict-sequence
runLSeqT_I :: L.Seq a -> [a]
runLSeqT_I = L.observeAll
{-# INLINABLE runLSeqT_I #-}

runLSeqT_S :: (forall s. L.SeqT (ST s) a) -> [a]
runLSeqT_S ma = runST (L.observeAllT ma)
{-# INLINABLE runLSeqT_S #-}

------------------------------------------------------------------------
-- Measured codes
heavy_right_assoc :: (MonadLogic m) => Int -> m ()
heavy_right_assoc n = heavy >>= guard
  where
    heavy = foldr (<|>) (return True) (replicate (n-1) (return False))
{-# INLINE heavy_right_assoc #-}

heavy_left_assoc :: (MonadLogic m) => Int -> m ()
heavy_left_assoc n = heavy >>= guard
  where
    falses = F.foldl (<|>) empty (replicate n (return False))
    heavy = falses <|> return True
{-# INLINE heavy_left_assoc #-}

heavy_treelike :: (MonadLogic m) => Int -> m ()
heavy_treelike n = go n True >>= guard
  where
    go k b
      | k <= 1 = return b
      | otherwise =
        let r = k `div` 2
            l = k - r
         in go l False <|> go r b
{-# INLINE heavy_treelike #-}

heavy_interleave :: (MonadLogic m) => Int -> m ()
heavy_interleave n = interleave heavy heavy >>= guard
  where
    m = n `div` 2
    heavy = foldr (<|>) (return True) (replicate (m-1) (return False))
{-# INLINE heavy_interleave #-}

heavy_fairbind :: (MonadLogic m) => Int -> m ()
heavy_fairbind n = heavy >>= guard
  where
    m = n `div` 5
    as = [1 .. 5] :: [Int]
    heavy =
      choose as >>- \k ->
        foldr (<|>) (return (k == 5)) (replicate m (return False))
{-# INLINE heavy_fairbind #-}

choose :: (Foldable t, Alternative f) => t a -> f a
choose = getAlt . foldMap (Alt . pure)
{-# INLINABLE choose #-}

-- Copied from post by u/dagit on:
--   https://www.reddit.com/r/haskell/comments/onwfr2/logictsequence_logict_empowered_by_reflection/
makeTree :: Int -> Tree Int
makeTree n = go 0
  where
    go k = Node k (go <$> filter (< n) [k * 3 + 1, k * 3 + 2, k * 3 + 3])

bfs :: MonadLogic m => Tree a -> m a
bfs t = go (pure t)
  where
    go q = do
      mb <- msplit q
      case mb of
        Nothing -> empty
        Just (m, qs) -> pure (rootLabel m) <|> go (qs <|> choose (subForest m))
{-# INLINABLE bfs #-}

heavy_bfs :: (MonadLogic m) => Int -> m ()
heavy_bfs n = bfs (makeTree n) >>= \k -> guard (k == n)
{-# INLINE heavy_bfs #-}

------------------------------------------------------------------------
-- Benchmark definition
main :: IO ()
main =
  defaultMain
    [ bgroup "right_assoc" (forEachMonad heavy_right_assoc),
      bgroup "left_assoc" (forEachMonad heavy_left_assoc),
      bgroup "treelike" (forEachMonad heavy_treelike),
      bgroup "interleave" (forEachMonad heavy_interleave),
      bgroup "fairbind" (forEachMonad heavy_fairbind),
      bgroup "bfs" (forEachMonad heavy_bfs)
    ]

forEachMonad :: (forall m. (MonadLogic m) => Int -> m ()) -> [Benchmark]
forEachMonad targetLogic =
  [ bgroup "[]" (forEachSize $ nf (runList . targetLogic)),
    bgroup "Seq" (forEachSize $ nf (runContainersSeq . targetLogic)),
    bgroup "ListT_I" (forEachSize $ nf (runListT_I . targetLogic)),
    bgroup "ListT_S" (forEachSize $ nf (\n -> runListT_S (targetLogic n))),
    bgroup "LogicT_I" (forEachSize $ nf (runLogicT_I . targetLogic)),
    bgroup "LogicT_S" (forEachSize $ nf (\n -> runLogicT_S (targetLogic n))),
    bgroup "L.SeqT_I" (forEachSize $ nf (\n -> runLSeqT_I (targetLogic n))),
    bgroup "L.SeqT_S" (forEachSize $ nf (\n -> runLSeqT_S (targetLogic n)))
  ]
{-# INLINE forEachMonad #-}

forEachSize :: (Int -> Benchmarkable) -> [Benchmark]
forEachSize f =
  map (\n -> bench (show n) $ f n) [100, 300, 1000, 3000, 10000]

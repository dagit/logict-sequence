{-# language ScopedTypeVariables #-}
{-# language DeriveGeneric #-}
{-# language FlexibleContexts #-}
{-# language UndecidableInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language DeriveFunctor #-}
{-# language StandaloneDeriving #-}
module Main(main) where

import Control.Monad.IO.Class (liftIO)
import Hedgehog (MonadGen, Range)
import qualified Hedgehog as HH
import qualified Hedgehog.Gen as Gen
import Hedgehog.Range (Size)
import qualified Hedgehog.Range as Range
import Test.Hspec (before, describe, hspec, it, shouldBe)
import Test.Hspec.Hedgehog (PropertyT, diff, forAll, hedgehog, (/==), (===))
import Control.Monad.Logic.Sequence
import qualified Control.Monad.Logic.Sequence.Compat as Compat
import Control.Monad.Logic.Sequence.Internal (SeqT (..))
import Data.SequenceClass hiding ((:<), empty)
import qualified Data.SequenceClass as S
import Control.Monad.Logic.Sequence.Internal.Queue
import Data.Functor.Identity
import Control.Applicative
import Data.Function (fix)
import GHC.Generics (Generic)
import qualified Hedgehog.Function as Fun
import Data.Foldable (foldl', for_)
import qualified Control.Monad.Logic as L
import Debug.Trace (trace)
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Morph (hoist)
import Control.Monad.ST
import Text.Read (readMaybe)

-- | A generic "container" functor. We can use this with `Free` to get
-- an inspectable `Monad` that's unlikely to hide any mistakes we make.
data TestF a = TestF !Int [a]
  deriving (Show, Read, Eq, Generic, Functor)

instance Fun.Arg a => Fun.Arg (TestF a)


-- Note: size
--
-- I've found it quite difficult to get a good range of
-- sizes for SeqT TestM Int using the basic tools in
-- Gen. Preventing almost all examples being tiny seems to lead to
-- some examples being unmanageably enormous. So I've decided to
-- go with a "nuclear option". First, I select the approximate total number
-- of nodes in the SeqT. Then at each stage, the approximate total size is
-- chosen in advance to make sure the target is met.

-- | Generate a partition of a non-negative integer into positive
-- integers. This is not statistically fair because I'm not that smart.
splat :: MonadGen m => Size -> m [Size]
splat 0 = pure []
splat n = do
  k <- Gen.integral (Range.constant 1 n)
  rest <- splat (n - k)
  pure (k : rest)

genTestFSized :: MonadGen m => (Size -> m a) -> Size -> m (TestF a)
genTestFSized m sz = do
  i <- Gen.integral (Range.constant 1 10000)
  part <- splat sz
  goop <- traverse m part
  pure (TestF i goop)

newtype TestM a = TestM (Free TestF a)
  deriving (Show, Read, Eq, Generic, Functor, Applicative, Monad)

genTestMSized :: MonadGen m => (Size -> m a) -> Size -> m (TestM a)
genTestMSized = \m sz -> TestM <$> go m sz
  where
    go :: MonadGen m => (Size -> m a) -> Size -> m (Free TestF a)
    go m n | n <= 1 = Pure <$> m (n - 1)
    go m n = Free <$> genTestFSized (go m) (n - 1)

-- | Generate a test monad value.
genTestM :: MonadGen m => m a -> m (TestM a)
genTestM m = Gen.sized $ \sz -> do
  true_size <- Gen.integral (Range.constant 0 sz)
  genTestMSized (const m) true_size

simpleTestM :: MonadGen m => m (TestM Int)
simpleTestM = genTestM (Gen.integral $ Range.constant 0 5)

listToQueue :: [a] -> Queue a
listToQueue = foldl' (S.|>) S.empty

genViewSized :: forall m a. MonadGen m => m a -> Size -> m (View TestM a)
genViewSized _ sz | sz <= 1 = pure Empty
genViewSized m sz = do
  a <- m
  s <- genSeqTSized m (sz - 1)
  pure (a :< s)

genSeqTSized :: forall m a. MonadGen m => m a -> Size -> m (SeqT TestM a)
genSeqTSized m sz = do
  part <- splat sz
  goop <- traverse (genTestMSized (genViewSized m)) part
  pure $ SeqT $ listToQueue goop

genSeqT :: forall m a. MonadGen m => m a -> m (SeqT TestM a)
genSeqT m = Gen.sized $ \sz -> do
  tsz <- Gen.integral (Range.linear 0 sz)
  genSeqTSized m tsz

simpleSeqT :: MonadGen m => m (SeqT TestM Int)
simpleSeqT = genSeqT (Gen.integral $ Range.constant 0 5)

main :: IO ()
main = hspec $ do
  describe "observe" $ do
    it "undoes pure" $ hedgehog $
      observe (pure (3 :: Int)) === Just 3
  describe "observeT" $ do
    it "undoes lift" $ hedgehog $ do
      ex <- forAll simpleTestM
      runMaybeT (Compat.observeT (lift (lift ex))) === runMaybeT (lift ex)
  describe "observeAllT" $ do
    it "undoes lift" $ hedgehog $ do
      ex <- forAll simpleTestM
      observeAllT (lift ex) === fmap (:[]) ex
    it "works like logicT" $ hedgehog $ do
      ex <- forAll simpleSeqT
      observeAllT ex === L.observeAllT (Compat.fromSeqT ex)
  describe "observeManyT" $ do
    it "takes at most n" $ hedgehog $ do
      n <- forAll $ Gen.integral (Range.linearFrom 0 (-100) 100)
      let alot :: SeqT (ST s) Int
          alot = pure n <|> alot
      length (runST (observeManyT n alot)) === max 0 n
    it "takes what it can" $ hedgehog $ do
      n <- forAll $ Gen.integral (Range.linearFrom 0 0 100)
      k <- forAll $ Gen.integral (Range.linearFrom 0 0 10)
      let alot :: Int -> SeqT (ST s) Int
          alot x | x <= 0 = empty
          alot x = pure x <|> alot (x-1)
      length (runST (observeManyT n (alot (n-k)))) === max 0 (n-k)
    it "in order" $ hedgehog $ do
      n <- forAll $ Gen.integral (Range.linearFrom 0 0 100)
      let alot :: Int -> SeqT (ST s) Int
          alot x | x <= 0 = empty
          alot x = pure x <|> alot (x-1)
      runST (observeManyT n (alot n)) === [n,(n-1)..1]
  describe "observeMany" $ do
    it "takes at most n" $ hedgehog $ do
      n <- forAll $ Gen.integral (Range.linearFrom 0 (-100) 100)
      let alot :: Seq Int
          alot = pure n <|> alot
      length (observeMany n alot) === max 0 n
    it "takes what it can" $ hedgehog $ do
      n <- forAll $ Gen.integral (Range.linearFrom 0 0 100)
      k <- forAll $ Gen.integral (Range.linearFrom 0 0 10)
      let alot :: Int -> Seq Int
          alot x | x <= 0 = empty
          alot x = pure x <|> alot (x-1)
      length (observeMany n (alot (n-k))) === max 0 (n-k)
    it "in order" $ hedgehog $ do
      n <- forAll $ Gen.integral (Range.linearFrom 0 0 100)
      let alot :: Int -> Seq Int
          alot x | x <= 0 = empty
          alot x = pure x <|> alot (x-1)
      observeMany n (alot n) === [n,(n-1)..1]
  describe "read" $ do
    it "undoes show" $ hedgehog $ do
      ex <- forAll simpleSeqT
      readMaybe (show ex) === Just ex
  describe ">>=" $ do
    it "obeys monad identity law 1" $ hedgehog $ do
      s <- forAll simpleSeqT
      (s >>= return) === s
    it "obeys monad identity law 2" $ hedgehog $ do
      a <- forAll $ Gen.integral Range.linearBounded
      f :: Int -> SeqT TestM Int <- Fun.forAllFn (Fun.fn simpleSeqT)
      (pure a >>= f) === f a
    it "works like LogicT" $ hedgehog $ do
      s <- forAll simpleSeqT
      f :: Int -> SeqT TestM Int <- Fun.forAllFn (Fun.fn simpleSeqT)
      Compat.fromLogicT (Compat.toLogicT s >>= Compat.toLogicT . f) === (s >>= f)
    it "obeys monad associativity law" $ hedgehog $ do
      s <- forAll simpleSeqT
      f :: Int -> SeqT TestM Int <- Fun.forAllFn (Fun.fn simpleSeqT)
      g :: Int -> SeqT TestM Int <- Fun.forAllFn (Fun.fn simpleSeqT)
      ((s >>= f) >>= g) === (s >>= \a -> f a >>= g)
    it "obeys left zero law" $ hedgehog $ do
      f :: Int -> SeqT TestM Int <- Fun.forAllFn (Fun.fn simpleSeqT)
      (empty >>= f) === empty
  describe "<|>" $ do
    it "is associative" $ hedgehog $ do
      s <- forAll (Gen.small simpleSeqT)
      t <- forAll (Gen.small simpleSeqT)
      u <- forAll (Gen.small simpleSeqT)
      ((s <|> t) <|> u) === (s <|> (t <|> u))
    it "obeys Alternative identity laws" $ hedgehog $ do
      s <- forAll (Gen.small simpleSeqT)
      (s <|> empty) === s
      (empty <|> s) === s
    it "obeys left distribution" $ hedgehog $ do
      s <- forAll (Gen.small simpleSeqT)
      t <- forAll (Gen.small simpleSeqT)
      f :: Int -> SeqT TestM Int <- Fun.forAllFn (Fun.fn simpleSeqT)
      ((s <|> t) >>= f) === ((s >>= f) <|> (t >>= f))
    it "works like LogicT" $ hedgehog $ do
      s <- forAll simpleSeqT
      t <- forAll simpleSeqT
      (s <|> t) === Compat.fromLogicT (Compat.fromSeqT s <|> Compat.fromSeqT t)
  describe "fromLogicT" $ do
    it "reverses fromSeqT" $ hedgehog $ do
      s <- forAll simpleSeqT
      Compat.fromLogicT (Compat.fromSeqT s) === s
  describe "fromView" $ do
    it "reverses toView" $ hedgehog $ do
      s <- forAll simpleSeqT
      fromView (toView s) === s
  describe "MonadReader instance" $ do
    it "passes the tests in https://github.com/Bodigrim/logict/issues/1" $ do
      runReader (runMaybeT (observeAllT (local (5+) ask))) 0 `shouldBe` Just [5]
      let
        foo :: MonadReader Int m => m (Int, Int)
        foo = do
          x <- local (5+) ask
          y <- ask
          return (x, y)
      runReader (runMaybeT (Compat.observeT foo)) 0 `shouldBe` Just (5, 0)
  describe "MFunctor instance" $ do
    it "obeys the hoist identity law" $ hedgehog $ do
      s <- forAll simpleSeqT
      hoist (\x -> x) s === s



-- -------
-- Reimplementation of Control.Monad.Free without the need
-- to futz with Data.Functor.Classes.

data Free f a = Pure a | Free (f (Free f a))
  deriving Functor
deriving instance (Show a, Show (f (Free f a))) => Show (Free f a)
deriving instance (Read a, Read (f (Free f a))) => Read (Free f a)
deriving instance (Eq a, Eq (f (Free f a))) => Eq (Free f a)
instance Functor f => Applicative (Free f) where
  pure = Pure
  (<*>) = ap
instance Functor f => Monad (Free f) where
  Pure a >>= f = f a
  Free ffa >>= f = Free $ (>>= f) <$> ffa

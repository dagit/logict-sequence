{-# LANGUAGE CPP #-}
#include "logict-sequence.h"
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

#ifdef USE_PATTERN_SYNONYMS
{-# LANGUAGE PatternSynonyms #-}
#endif

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Trustworthy #-}
#endif
{-# OPTIONS_HADDOCK not-home #-}

module Control.Monad.Logic.Sequence.Internal
(
#ifdef USE_PATTERN_SYNONYMS
    SeqT(MkSeqT, getSeqT, ..)
#else
    SeqT(..)
#endif
  , Seq
#ifdef USE_PATTERN_SYNONYMS
  , pattern MkSeq
  , getSeq
#endif
  , View(..)
  , toView
  , fromView
  , observeAllT
  , observeAll
  , observeManyT
  , observeMany
  , observeT
  , observe
  , fromSeqT
  , hoistPre
  , hoistPost
  , hoistPreUnexposed
  , hoistPostUnexposed
  , toLogicT
  , fromLogicT
  , chooseStreamM
  , chooseSeqT
  , cons
  , consM
  , choose
  , chooseM
)
where

import Control.Applicative as A
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Monad.Identity (Identity(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Logic.Class
import qualified Control.Monad.Logic as L
import Control.Monad.IO.Class
import Control.Monad.Reader.Class (MonadReader (..))
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Morph (MFunctor (..))
import qualified Data.SequenceClass as S
import Control.Monad.Logic.Sequence.Internal.Queue (Queue)
import qualified Text.Read as TR
import Data.Function (on)
#if MIN_VERSION_base(4,9,0)
import Data.Functor.Classes
#endif

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid(..))
#endif

#if MIN_VERSION_base(4,9,0)
import Data.Semigroup (Semigroup(..))
#endif

import qualified Data.Foldable as F
import GHC.Generics (Generic)


-- | Based on the LogicT improvements in the paper, Reflection without
-- Remorse. Code is based on the code provided in:
-- https://github.com/atzeus/reflectionwithoutremorse
--
-- Note: that code is provided under an MIT license, so we use that as
-- well.

data View m a = Empty | a :< SeqT m a
  deriving Generic
infixl 5 :<

deriving instance (Show a, Show (SeqT m a)) => Show (View m a)
deriving instance (Read a, Read (SeqT m a)) => Read (View m a)
deriving instance (Eq a, Eq (SeqT m a)) => Eq (View m a)
deriving instance (Ord a, Ord (SeqT m a)) => Ord (View m a)
deriving instance Monad m => Functor (View m)

#if MIN_VERSION_base(4,9,0)
instance (Eq1 m, Monad m) => Eq1 (View m) where
  liftEq _ Empty Empty = True
  liftEq eq (a :< s) (b :< t) = eq a b && liftEq eq s t
  liftEq _ _ _ = False

instance (Ord1 m, Monad m) => Ord1 (View m) where
  liftCompare _ Empty Empty = EQ
  liftCompare _ Empty (_ :< _) = LT
  liftCompare cmp (a :< s) (b :< t) = cmp a b `mappend` liftCompare cmp s t
  liftCompare _ (_ :< _) Empty = GT

instance (Show1 m, Monad m) => Show1 (View m) where
  liftShowsPrec sp sl d val = case val of
    Empty -> ("Empty" ++)
    a :< s -> showParen (d > 5) $
      sp 6 a .
      showString " :< " .
      liftShowsPrec sp sl 6 s
#endif

-- | An asymptotically efficient logic monad transformer. It is generally best to
-- think of this as being defined
--
-- @
-- newtype SeqT m a = 'MkSeqT' { 'getSeqT' :: m ('View' m a) }
-- @
--
-- Using the 'MkSeqT' pattern synonym with 'getSeqT', you can (almost) pretend
-- it's really defined this way! However, the real implementation is different,
-- so as to be more efficient in the face of deeply left-associated `<|>` or
-- `mplus` applications.
newtype SeqT m a = SeqT { runSeqT :: (Queue (m (View m a))) }

#ifdef USE_PATTERN_SYNONYMS
pattern MkSeqT :: Monad m => m (View m a) -> SeqT m a
pattern MkSeqT{getSeqT} <- (toView -> getSeqT)
  where
    MkSeqT = fromView
{-# COMPLETE MkSeqT #-}

pattern MkSeq :: View Identity a -> Seq a
pattern MkSeq{getSeq} <- (runIdentity . toView -> getSeq)
  where
    MkSeq = fromView . Identity
{-# COMPLETE MkSeq #-}
#endif

-- | A specialization of 'SeqT' to the 'Identity' monad. You can
-- imagine that this is defined
--
-- @
-- newtype Seq a = MkSeq { getSeq :: View Identity a }
-- @
--
-- Using the 'MkSeq' pattern synonym with 'getSeq', you can pretend it's
-- really defined this way! However, the real implementation is different,
-- so as to be more efficient in the face of deeply left-associated `<|>`
-- or `mplus` applications.
type Seq = SeqT Identity

fromView :: m (View m a) -> SeqT m a
fromView = SeqT . S.singleton
{-# INLINE[0] fromView #-}

toView :: Monad m => SeqT m a -> m (View m a)
toView (SeqT s0) = go s0 where
  go s = case S.viewl s of
    S.EmptyL -> return Empty
    h S.:< t -> h >>= \x -> case x of
      Empty -> go t
      hi :< SeqT ti -> return (hi :< SeqT (ti S.>< t))
{-# INLINE[0] toView #-}

data Step s a = Done | Yield a s | Skip s
data StreamM m a = forall s. StreamM (s -> m (Step s a)) s

stream :: Monad m => SeqT m a -> StreamM m a
stream m = StreamM next m where
  {-# INLINE next #-}
  next s = do
    x <- toView s
    case x of
      Empty -> return Done
      h :< t -> return (Yield h t)
{-# INLINE[1] stream #-}

unstream :: Monad m => StreamM m a -> SeqT m a
unstream (StreamM next s0) = fromView (unfold s0)
  where
  unfold s = do
    v <- next s
    case v of
      Done -> return Empty
      Skip xs -> unfold xs
      Yield x xs -> return (x :< fromView (unfold xs))
{-# INLINE[1] unstream #-}

{-# RULES
      "stream-unstream" [2] forall s. stream (unstream s) = s;
  #-}

{-
Theorem: toView . fromView = id

Proof:

toView (fromView m)
=
toView (SeqT (singleton m))
=
case viewl (singleton m) of
    h S.:< t -> h >>= \x -> case x of
      Empty -> toView (SeqT t)
      hi :< SeqT ti -> return (hi :< SeqT (ti S.>< t))
=
m >>= \x -> case x of
  Empty -> toView (SeqT S.empty)
  hi :< SeqT ti -> return (hi :< SeqT ti)
=
m >>= \x -> case x of
  Empty -> return Empty
  hi :< SeqT ti -> return (hi :< SeqT ti)
= m
-}

newtype Fix1 f a = In1 { out1 :: f (Fix1 f a) a }

chooseStreamM :: (F.Foldable f, Monad m) => f a -> StreamM m a
chooseStreamM = StreamM (return . out1) . F.foldr (\a b -> In1 (Yield a b)) (In1 Done)
{-# INLINE[1] chooseStreamM #-}

chooseSeqT :: (F.Foldable f, Monad m) => f a -> SeqT m a
chooseSeqT = unstream . chooseStreamM
{-# INLINE[3] chooseSeqT #-}

instance (Show (m (View m a)), Monad m) => Show (SeqT m a) where
  showsPrec d s = showParen (d > app_prec) $
      showString "MkSeqT " . showsPrec (app_prec + 1) (toView s)
    where app_prec = 10

instance Read (m (View m a)) => Read (SeqT m a) where
  readPrec = TR.parens $ TR.prec app_prec $ do
      TR.Ident "MkSeqT" <- TR.lexP
      m <- TR.step TR.readPrec
      return (fromView m)
    where app_prec = 10
  readListPrec = TR.readListPrecDefault

instance (Eq a, Eq (m (View m a)), Monad m) => Eq (SeqT m a) where
  (==) = (==) `on` toView
instance (Ord a, Ord (m (View m a)), Monad m) => Ord (SeqT m a) where
  compare = compare `on` toView


#if MIN_VERSION_base(4,9,0)
instance (Eq1 m, Monad m) => Eq1 (SeqT m) where
  liftEq eq s t = liftEq (liftEq eq) (toView s) (toView t)

instance (Ord1 m, Monad m) => Ord1 (SeqT m) where
  liftCompare eq s t = liftCompare (liftCompare eq) (toView s) (toView t)

instance (Show1 m, Monad m) => Show1 (SeqT m) where
  liftShowsPrec sp sl d s = showParen (d > app_prec) $
      showString "MkSeqT " . liftShowsPrec (liftShowsPrec sp sl) (liftShowList sp sl) (app_prec + 1) (toView s)
    where app_prec = 10
#endif

single :: Monad m => a -> m (View m a)
single a = return (a :< mzero)
{-# INLINE single #-}

instance Monad m => Functor (SeqT m) where
  {-# INLINEABLE fmap #-}
  fmap = fmapSeqT

fmapSeqT :: Monad m => (a -> b) -> SeqT m a -> SeqT m b
fmapSeqT f s = unstream (fmap_s f (stream s))
{-# INLINEABLE [3] fmapSeqT #-}

fmap_s :: Monad m => (a -> b) -> StreamM m a -> StreamM m b
fmap_s f (StreamM next_a a0) = StreamM next a0
  where
  {-# INLINE next #-}
  next a = do
    x <- next_a a
    case x of
      Done -> return Done
      Skip s -> return (Skip s)
      Yield y ys -> return (Yield (f y) ys)
{-# INLINEABLE [1] fmap_s #-}

instance Monad m => Applicative (SeqT m) where
  {-# INLINE pure #-}
  {-# INLINABLE (<*>) #-}
  pure = fromView . single
  (<*>) = ap
  (*>) = (>>)
#if MIN_VERSION_base(4,10,0)
  liftA2 = liftM2
  {-# INLINABLE liftA2 #-}
#endif

instance Monad m => Alternative (SeqT m) where
  {-# INLINE empty #-}
  {-# INLINEABLE (<|>) #-}
  empty = SeqT S.empty
  (<|>) = alt

alt :: Monad m => SeqT m a -> SeqT m a -> SeqT m a
alt a b = unstream (alt_s (stream a) (stream b))
{-# INLINE[3] alt #-}

alt_s :: Monad m => StreamM m a -> StreamM m a -> StreamM m a
alt_s (StreamM next_a a) (StreamM next_b b) = StreamM next (Just a, b)
  where
  {-# INLINE next #-}
  next (Nothing, s_b) = do
    x <- next_b s_b
    return $ case x of
      Done -> Done
      Skip vs -> Skip (Nothing, vs)
      Yield v vs -> Yield v (Nothing, vs)
  next (Just s_a, s_b) = do
    y <- next_a s_a
    case y of
      Done -> do
        x <- next_b s_b
        return $ case x of
          Done -> Done
          Skip vs -> Skip (Nothing, vs)
          Yield v vs -> Yield v (Nothing, vs)
      Skip vs -> return (Skip (Just vs, s_b))
      Yield x xs -> return (Yield x (Just xs, s_b))
{-# INLINE[1] alt_s #-}

-- | @cons a s = pure a <|> s@
cons :: Monad m => a -> SeqT m a -> SeqT m a
cons a s = fromView (return (a :< s))
{-# INLINE cons #-}

-- | @consM m s = lift m <|> s@
consM :: Monad m => m a -> SeqT m a -> SeqT m a
consM m s = fromView (liftM (:< s) m)
{-# INLINE consM #-}

instance Monad m => Monad (SeqT m) where
  {-# INLINE return #-}
  {-# INLINEABLE (>>=) #-}
  return = fromView . single
  (>>=) = bind
#if !MIN_VERSION_base(4,13,0)
  {-# INLINEABLE fail #-}
  fail = Fail.fail
#endif

bind :: Monad m => SeqT m a -> (a -> SeqT m b) -> SeqT m b
bind m f = unstream (bind_s (stream m) (stream . f))
{-# INLINE[3] bind #-}

data BindSState a b m
  = Boundary a
  | forall s. InProgress a (s -> m (Step s b)) s

bind_s :: Monad m => StreamM m a -> (a -> StreamM m b) -> StreamM m b
bind_s (StreamM next_a a0) f = StreamM next (Boundary a0) where
  next _ = return undefined
-- TODO: fixme: this is an infinite loop right now
{-
  {-# INLINE next #-}
  next (Boundary s_a) = do
    x <- next_a s_a
    return $ case x of
      Yield a _ -> case f a of
        StreamM next_fa fa0 -> Skip (InProgress s_a next_fa fa0)
      Skip as -> Skip (Boundary as)
      Done -> Done
  next (InProgress s_a next_fa s_fa) = do
    x <- next_fa s_fa
    return $ case x of
      Yield b bs -> Yield b (InProgress s_a next_fa bs)
      Skip bs -> Skip (InProgress s_a next_fa bs)
      Done -> Skip (Boundary s_a)
-}
{-# INLINE[1] bind_s #-}

instance Monad m => Fail.MonadFail (SeqT m) where
  {-# INLINEABLE fail #-}
  fail _ = SeqT S.empty

instance Monad m => MonadPlus (SeqT m) where
  {-# INLINE mzero #-}
  {-# INLINE mplus #-}
  mzero = A.empty
  mplus = (<|>)

#if MIN_VERSION_base(4,9,0)
instance Monad m => Semigroup (SeqT m a) where
  {-# INLINE (<>) #-}
  {-# INLINE sconcat #-}
  (<>) = mplus
  sconcat = foldr1 mplus
#endif

instance Monad m => Monoid (SeqT m a) where
  {-# INLINE mempty #-}
  {-# INLINE mappend #-}
  {-# INLINE mconcat #-}
  mempty = SeqT S.empty
  mappend = (<|>)
  mconcat = F.asum

instance MonadTrans SeqT where
  {-# INLINE lift #-}
  lift m = fromView (m >>= single)

instance Monad m => MonadLogic (SeqT m) where
  {-# INLINE[3] msplit #-}
  msplit (toView -> m) = fromView $ do
    r <- m
    case r of
      Empty -> single Nothing
      a :< t -> single (Just (a, t))

-- | @choose = foldr (\a s -> pure a <|> s) empty@
--
-- @choose :: Monad m => [a] -> SeqT m a@
choose :: (F.Foldable t, Monad m) => t a -> SeqT m a
choose = F.foldr cons empty
{-# INLINABLE choose #-}

-- | @chooseM = foldr (\ma s -> lift ma <|> s) empty@
--
-- @chooseM :: Monad m => [m a] -> SeqT m a@
chooseM :: (F.Foldable t, Monad m) => t (m a) -> SeqT m a
-- The idea here, which I hope is sensible, is to avoid building and
-- restructuring queues unnecessarily. We end up building only *singleton*
-- queues, which should hopefully be pretty cheap.
chooseM = F.foldr consM empty
{-# INLINABLE chooseM #-}

observeAllT :: Monad m => SeqT m a -> m [a]
observeAllT (toView -> m) = m >>= go where
  go (a :< t) = liftM (a:) (toView t >>= go)
  go _ = return []
{-# INLINEABLE observeAllT #-}

observeT :: Monad m => SeqT m a -> m (Maybe a)
observeT (toView -> m) = m >>= go where
  go (a :< _) = return (Just a)
  go Empty = return Nothing
{-# INLINE observeT #-}

observeManyT :: Monad m => Int -> SeqT m a -> m [a]
observeManyT k m = toView m >>= go k where
  go n _ | n <= 0 = return []
  go _ Empty = return []
  go n (a :< t) = liftM (a:) (observeManyT (n-1) t)
{-# INLINEABLE observeManyT #-}

observe :: Seq a -> Maybe a
observe = runIdentity . observeT
{-# INLINE observe #-}

observeAll :: Seq a -> [a]
observeAll = runIdentity . observeAllT
{-# INLINE observeAll #-}

observeMany :: Int -> Seq a -> [a]
observeMany n = runIdentity . observeManyT n
{-# INLINE observeMany #-}

-- | Convert @'SeqT' m a@ to @t m a@ when @t@ is some other logic monad
-- transformer.
fromSeqT :: (Monad m, Monad (t m), MonadTrans t, Alternative (t m)) => SeqT m a -> t m a
fromSeqT (toView -> m) = lift m >>= \r -> case r of
  Empty -> empty
  a :< s -> pure a <|> fromSeqT s

-- | Convert @'SeqT' m a@ to @'L.LogicT' m a@.
--
-- @ toLogicT = 'fromSeqT' @
toLogicT :: Monad m => SeqT m a -> L.LogicT m a
toLogicT = fromSeqT

fromLogicT :: Monad m => L.LogicT m a -> SeqT m a
fromLogicT (L.LogicT f) = fromView $ f (\a v -> return (a :< fromView v)) (return Empty)

-- | 'hoist' is 'hoistPre'.
instance MFunctor SeqT where
  -- Note: if `f` is not a monad morphism, then hoist may not respect
  -- (==). That is, it could be that
  --
  --   s == t = True
  --
  --  but
  --
  --   hoist f s == hoist f t = False..
  --
  -- This behavior is permitted by the MFunctor
  -- documentation, and allows us to avoid restructuring
  -- the SeqT.
  hoist f = hoistPre f

-- | This function is the implementation of 'hoist' for 'SeqT'. The passed
-- function is required to be a monad morphism.
hoistPre :: Monad m => (forall x. m x -> n x) -> SeqT m a -> SeqT n a
hoistPre f (SeqT s) = SeqT $ fmap (f . liftM go) s
  where
    go Empty = Empty
    go (a :< as) = a :< hoistPre f as

-- | A version of `hoist` that uses the `Monad` instance for @n@
-- rather than for @m@. Like @hoist@, the passed function is required
-- to be a monad morphism.
hoistPost :: Monad n => (forall x. m x -> n x) -> SeqT m a -> SeqT n a
hoistPost f (SeqT s) = SeqT $ fmap (liftM go . f) s
  where
      go Empty = Empty
      go (a :< as) = a :< hoistPost f as

-- | A version of 'hoist' that works for arbitrary functions, rather
-- than just monad morphisms.
hoistPreUnexposed :: forall m n a. Monad m => (forall x. m x -> n x) -> SeqT m a -> SeqT n a
hoistPreUnexposed f (toView -> m) = fromView $ f (liftM go m)
  where
      go Empty = Empty
      go (a :< as) = a :< hoistPreUnexposed f as

-- | A version of 'hoistPost' that works for arbitrary functions, rather
-- than just monad morphisms. This should be preferred when the `Monad` instance
-- for `n` is less expensive than that for `m`.
hoistPostUnexposed :: forall m n a. (Monad m, Monad n) => (forall x. m x -> n x) -> SeqT m a -> SeqT n a
hoistPostUnexposed f (toView -> m) = fromView $ liftM go (f m)
  where
      go Empty = Empty
      go (a :< as) = a :< hoistPostUnexposed f as

instance MonadIO m => MonadIO (SeqT m) where
  {-# INLINE liftIO #-}
  liftIO = lift . liftIO

instance MonadReader e m => MonadReader e (SeqT m) where
  -- TODO: write more thorough tests for this instance (issue #31)
  ask = lift ask
  local f (SeqT q) = SeqT $ fmap (local f . liftM go) q
    where
      go Empty = Empty
      go (a :< s) = a :< local f s

instance MonadState s m => MonadState s (SeqT m) where
  get = lift get
  put = lift . put
  state = lift . state

instance MonadError e m => MonadError e (SeqT m) where
  -- TODO: write tests for this instance (issue #31)
  throwError = lift . throwError
  catchError (toView -> m) h = fromView $ (liftM go m) `catchError` (toView . h)
    where
      go Empty = Empty
      go (a :< s) = a :< catchError s h

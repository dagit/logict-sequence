{-# LANGUAGE CPP #-}
#include "logict-sequence.h"
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
#if __GLASGOW_HASKELL__ < 710
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
#endif
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
{- OPTIONS_GHC -ddump-simpl -dsuppress-coercions #-}

-- | Based on the LogicT improvements in the paper, Reflection without
-- Remorse. Code is based on the code provided in:
-- https://github.com/atzeus/reflectionwithoutremorse
--
-- Note: that code is provided under an MIT license, so we use that as
-- well.
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
  , ViewT(..)
  , View
  , viewT
  , view
  , toViewT
  , toView
  , fromViewT
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
  , cons
  , consM
  , choose
  , chooseM
)
where

import Control.Applicative
import Control.Monad hiding (liftM)
#if !MIN_VERSION_base(4,8,0)
import qualified Control.Monad as Monad
#endif
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
#if MIN_VERSION_base(4,8,0)
import Control.Monad.Zip (MonadZip (..))
#endif
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
import qualified Data.Traversable as T
import GHC.Generics (Generic)
import Data.Coerce (coerce)

-- | A view of the front end of a 'SeqT'.
data ViewT m a = Empty | a :< SeqT m a
  deriving Generic
infixl 5 :<

type View = ViewT Identity

-- | A catamorphism for 'ViewT's
viewT :: b -> (a -> SeqT m a -> b) -> ViewT m a -> b
viewT n _ Empty = n
viewT _ c (a :< s) = c a s
{-# INLINE viewT #-}

-- | A catamorphism for 'View's. Note that this is just a type-restricted version
-- of 'viewT'.
view :: b -> (a -> Seq a -> b) -> View a -> b
view = viewT
{-# INLINE view #-}

deriving instance (Show a, Show (SeqT m a)) => Show (ViewT m a)
deriving instance (Read a, Read (SeqT m a)) => Read (ViewT m a)
deriving instance (Eq a, Eq (SeqT m a)) => Eq (ViewT m a)
deriving instance (Ord a, Ord (SeqT m a)) => Ord (ViewT m a)
deriving instance Monad m => Functor (ViewT m)
deriving instance (Monad m, F.Foldable m) => F.Foldable (ViewT m)
instance (Monad m, T.Traversable m) => T.Traversable (ViewT m) where
  traverse _ Empty = pure Empty
  traverse f (x :< xs) =
    liftA2 (\y ys -> y :< fromViewT ys) (f x) (T.traverse (T.traverse f) . toViewT $ xs)
--  The derived instance would use
--
--    traverse f (x :< xs) = liftA2 (:<) (f x) (traverse f xs)
--
--  Inlining the inner `traverse` reveals an application of `fmap` which
--  we fuse with `liftA2`, in case `fmap` isn't free.

#if MIN_VERSION_base(4,9,0)
instance (Eq1 m, Monad m) => Eq1 (ViewT m) where
  liftEq _ Empty Empty = True
  liftEq eq (a :< s) (b :< t) = eq a b && liftEq eq s t
  liftEq _ _ _ = False

instance (Ord1 m, Monad m) => Ord1 (ViewT m) where
  liftCompare _ Empty Empty = EQ
  liftCompare _ Empty (_ :< _) = LT
  liftCompare cmp (a :< s) (b :< t) = cmp a b `mappend` liftCompare cmp s t
  liftCompare _ (_ :< _) Empty = GT

instance (Show1 m, Monad m) => Show1 (ViewT m) where
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
-- newtype SeqT m a = 'MkSeqT' { 'getSeqT' :: m ('ViewT' m a) }
-- @
--
-- Using the 'MkSeqT' pattern synonym with 'getSeqT', you can (almost) pretend
-- it's really defined this way! However, the real implementation is different,
-- so as to be more efficient in the face of deeply left-associated `<|>` or
-- `mplus` applications.
newtype SeqT m a = SeqT (Queue (m (ViewT m a)))

#ifdef USE_PATTERN_SYNONYMS
pattern MkSeqT :: Monad m => m (ViewT m a) -> SeqT m a
pattern MkSeqT{getSeqT} <- (toViewT -> getSeqT)
  where
    MkSeqT = fromViewT
{-# COMPLETE MkSeqT #-}

pattern MkSeq :: View a -> Seq a
pattern MkSeq{getSeq} = MkSeqT (Identity getSeq)
{-# COMPLETE MkSeq #-}
#endif

-- | A specialization of 'SeqT' to the 'Identity' monad. You can
-- imagine that this is defined
--
-- @
-- newtype Seq a = MkSeq { getSeq :: ViewT Identity a }
-- @
--
-- Using the 'MkSeq' pattern synonym with 'getSeq', you can pretend it's
-- really defined this way! However, the real implementation is different,
-- so as to be more efficient in the face of deeply left-associated `<|>`
-- or `mplus` applications.
type Seq = SeqT Identity

fromViewT :: m (ViewT m a) -> SeqT m a
fromViewT = SeqT . S.singleton
{-# INLINE [1] fromViewT #-}

fromView :: forall a. View a -> Seq a
fromView = coerce (fromViewT :: Identity (View a) -> Seq a)
{-# INLINE fromView #-}

toViewT :: Monad m => SeqT m a -> m (ViewT m a)
toViewT (SeqT s) = case S.viewl s of
  S.EmptyL -> return Empty
  h S.:< t -> h >>= \x -> case x of
    Empty -> toViewT (SeqT t)
    hi :< SeqT ti -> return (hi :< SeqT (ti S.>< t))
{-# INLINEABLE [1] toViewT #-}

toView :: forall a. Seq a -> View a
toView = coerce (toViewT :: SeqT Identity a -> Identity (ViewT Identity a))
{-# INLINABLE toView #-}

-- For now, we don't assume the monad identity law holds for the underlying
-- monad. We may re-evaluate that later, but it's a bit tricky to document the
-- detailed strictness requirements properly.
--
-- We do, however, assume that `pure /= _|_`, or that `>>=` doesn't `seq` on
-- its second argument, and that we can therefore eta-reduce `\x -> pure x` to
-- just `pure`. It seems quite safe to assume that at least one of these is
-- true, since in real code they're virtually always *both* true.
{-# RULES
"toViewT . fromViewT" forall m. toViewT (fromViewT m) = m >>= return
 #-}

{-
Theorem: toViewT . fromViewT = id

Proof:

toViewT (fromViewT m)
=
toViewT (SeqT (singleton m))
=
case viewl (singleton m) of
    h S.:< t -> h >>= \x -> case x of
      Empty -> toViewT (SeqT t)
      hi :< SeqT ti -> return (hi :< SeqT (ti S.>< t))
=
m >>= \x -> case x of
  Empty -> toViewT (SeqT S.empty)
  hi :< SeqT ti -> return (hi :< SeqT ti)
=
m >>= \x -> case x of
  Empty -> return Empty
  hi :< SeqT ti -> return (hi :< SeqT ti)
= m >>= \x -> return x
= m -- assuming the appropriate identity law holds for the underlying monad.
-}

instance (Show (m (ViewT m a)), Monad m) => Show (SeqT m a) where
  showsPrec d s = showParen (d > app_prec) $
      showString "MkSeqT " . showsPrec (app_prec + 1) (toViewT s)
    where app_prec = 10

instance Read (m (ViewT m a)) => Read (SeqT m a) where
  readPrec = TR.parens $ TR.prec app_prec $ do
      TR.Ident "MkSeqT" <- TR.lexP
      m <- TR.step TR.readPrec
      return (fromViewT m)
    where app_prec = 10
  readListPrec = TR.readListPrecDefault

instance (Eq a, Eq (m (ViewT m a)), Monad m) => Eq (SeqT m a) where
  (==) = (==) `on` toViewT
instance (Ord a, Ord (m (ViewT m a)), Monad m) => Ord (SeqT m a) where
  compare = compare `on` toViewT


#if MIN_VERSION_base(4,9,0)
instance (Eq1 m, Monad m) => Eq1 (SeqT m) where
  liftEq eq s t = liftEq (liftEq eq) (toViewT s) (toViewT t)

instance (Ord1 m, Monad m) => Ord1 (SeqT m) where
  liftCompare eq s t = liftCompare (liftCompare eq) (toViewT s) (toViewT t)

instance (Show1 m, Monad m) => Show1 (SeqT m) where
  liftShowsPrec sp sl d s = showParen (d > app_prec) $
      showString "MkSeqT " . liftShowsPrec (liftShowsPrec sp sl) (liftShowList sp sl) (app_prec + 1) (toViewT s)
    where app_prec = 10
#endif

single :: Monad m => a -> m (ViewT m a)
single a = return (a :< mzero)
{-# INLINE single #-}

instance Monad m => Functor (SeqT m) where
  {-# INLINEABLE fmap #-}
  fmap f (SeqT q) = SeqT $ fmap (myliftM (fmap f)) q
  {-# INLINABLE (<$) #-}
  x <$ SeqT q = SeqT $ fmap (myliftM (x <$)) q

instance Monad m => Applicative (SeqT m) where
  {-# INLINE pure #-}
  {-# INLINABLE (<*>) #-}
  pure = fromViewT . single

#if MIN_VERSION_base(4,8,0)
  fs <*> xs = fs >>= \f -> f <$> xs
#else
  (<*>) = ap
#endif

  {-# INLINEABLE (*>) #-}
  (toViewT -> m) *> n = fromViewT $ m >>= \x -> case x of
    Empty -> return Empty
    _ :< t -> n `altViewT` (t *> n)

#if MIN_VERSION_base(4,10,0)
  liftA2 f xs ys = xs >>= \x -> f x <$> ys
  {-# INLINABLE liftA2 #-}
#endif

instance Monad m => Alternative (SeqT m) where
  {-# INLINE empty #-}
  {-# INLINEABLE (<|>) #-}
  empty = SeqT S.empty
  m <|> n = fromViewT (altViewT m n)

altViewT :: Monad m => SeqT m a -> SeqT m a -> m (ViewT m a)
altViewT (toViewT -> m) n = m >>= \x -> case x of
  Empty -> toViewT n
  h :< t -> return (h :< cat t n)
    where cat (SeqT l) (SeqT r) = SeqT (l S.>< r)
{-# INLINE altViewT #-}

-- | @cons a s = pure a <|> s@
cons :: Monad m => a -> SeqT m a -> SeqT m a
cons a s = fromViewT (return (a :< s))
{-# INLINE cons #-}

-- | @consM m s = lift m <|> s@
consM :: Monad m => m a -> SeqT m a -> SeqT m a
consM m s = fromViewT (myliftM (:< s) m)
{-# INLINE consM #-}

instance Monad m => Monad (SeqT m) where
  {-# INLINE return #-}
  {-# INLINEABLE (>>=) #-}
  return = pure
  (toViewT -> m) >>= f = fromViewT $ m >>= \x -> case x of
    Empty -> return Empty
    h :< t -> f h `altViewT` (t >>= f)
  (>>) = (*>)

#if !MIN_VERSION_base(4,13,0)
  {-# INLINEABLE fail #-}
  fail = Fail.fail
#endif

instance Monad m => Fail.MonadFail (SeqT m) where
  {-# INLINEABLE fail #-}
  fail _ = SeqT S.empty

instance Monad m => MonadPlus (SeqT m) where
  {-# INLINE mzero #-}
  {-# INLINE mplus #-}
  mzero = Control.Applicative.empty
  mplus = (<|>)

#if MIN_VERSION_base(4,9,0)
instance Monad m => Semigroup (SeqT m a) where
  {-# INLINE (<>) #-}
  {-# INLINE sconcat #-}
  (<>) = mplus
  sconcat = F.asum
#endif

instance Monad m => Monoid (SeqT m a) where
  {-# INLINE mempty #-}
  {-# INLINE mconcat #-}
  mempty = SeqT S.empty
  mconcat = F.asum
#if !MIN_VERSION_base(4,9,0)
  {-# INLINE mappend #-}
  mappend = (<|>)
#endif

instance MonadTrans SeqT where
  {-# INLINE lift #-}
  lift m = fromViewT (m >>= single)

instance Monad m => MonadLogic (SeqT m) where
  {-# INLINE msplit #-}
  msplit (toViewT -> m) = fromViewT $ do
    r <- m
    case r of
      Empty -> single Nothing
      a :< t -> single (Just (a, t))

  interleave m1 m2 = fromViewT $ interleaveViewT m1 m2

  (toViewT -> m) >>- f = fromViewT $ m >>= viewT
     (return Empty) (\a m' -> interleaveViewT (f a) (m' >>- f))

  ifte (toViewT -> t) th (toViewT -> el) = fromViewT $ t >>= viewT
    el
    (\a s -> altViewT (th a) (s >>= th))

  once (toViewT -> m) = fromViewT $ m >>= viewT
    (return Empty)
    (\a _ -> single a)

  lnot (toViewT -> m) = fromViewT $ m >>= viewT
    (single ()) (\ _ _ -> return Empty)

-- | A version of 'interleave' that produces a view instead of a
-- 'SeqT'. This lets us avoid @toViewT . fromViewT@ in '>>-'.
interleaveViewT :: Monad m => SeqT m a -> SeqT m a -> m (ViewT m a)
interleaveViewT (toViewT -> m1) m2 = m1 >>= viewT
  (toViewT m2)
  (\a m1' -> return $ a :< interleave m2 m1')

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

-- | Perform all the actions in a 'SeqT' and gather the results.
observeAllT :: Monad m => SeqT m a -> m [a]
observeAllT (toViewT -> m) = m >>= go where
  go (a :< t) = myliftM (a:) (toViewT t >>= go)
  go _ = return []
{-# INLINEABLE observeAllT #-}

-- | Perform actions in a 'SeqT' until one of them produces a
-- result. Returns 'Nothing' if there are no results.
observeT :: Monad m => SeqT m a -> m (Maybe a)
observeT (toViewT -> m) = m >>= go where
  go (a :< _) = return (Just a)
  go Empty = return Nothing
{-# INLINE observeT #-}

-- | @observeManyT n s@ performs actions in @s@ until it produces
-- @n@ results or terminates. All the gathered results are returned.
observeManyT :: Monad m => Int -> SeqT m a -> m [a]
observeManyT k m = toViewT m >>= go k where
  go n _ | n <= 0 = return []
  go _ Empty = return []
  go n (a :< t) = myliftM (a:) (observeManyT (n-1) t)
{-# INLINEABLE observeManyT #-}

-- | Get the first result in a 'Seq', if there is one.
observe :: Seq a -> Maybe a
observe = runIdentity . observeT
{-# INLINE observe #-}

-- | Get all the results in a 'Seq'.
observeAll :: Seq a -> [a]
observeAll = runIdentity . observeAllT
{-# INLINE observeAll #-}

-- | @observeMany n s@ gets up to @n@ results from a 'Seq'.
observeMany :: Int -> Seq a -> [a]
observeMany n = runIdentity . observeManyT n
{-# INLINE observeMany #-}

-- | Convert @'SeqT' m a@ to @t m a@ when @t@ is some other logic monad
-- transformer.
fromSeqT :: (Monad m, Monad (t m), MonadTrans t, Alternative (t m)) => SeqT m a -> t m a
fromSeqT (toViewT -> m) = lift m >>= \r -> case r of
  Empty -> empty
  a :< s -> pure a <|> fromSeqT s

-- | Convert @'SeqT' m a@ to @'L.LogicT' m a@.
--
-- @ toLogicT = 'fromSeqT' @
toLogicT :: Monad m => SeqT m a -> L.LogicT m a
toLogicT = fromSeqT

fromLogicT :: Monad m => L.LogicT m a -> SeqT m a
fromLogicT (L.LogicT f) = fromViewT $ f (\a v -> return (a :< fromViewT v)) (return Empty)

instance (Monad m, F.Foldable m) => F.Foldable (SeqT m) where
  foldMap f = F.foldMap (F.foldMap f) . toViewT

instance (Monad m, T.Traversable m) => T.Traversable (SeqT m) where
  -- Why is this lawful? It comes down to the fact that toViewT and
  -- fromViewT are inverses, modulo representation and detailed
  -- strictness. They witness a sort of stepwise isomorphism between
  -- SeqT and the obviously traversable
  --
  --   newtype ML m a = ML (m (ViewT m a))
  --
  -- Why can't we just use the derived Traversable instance? It doesn't
  -- respect ==. See https://github.com/dagit/logict-sequence/issues/51#issuecomment-896242724
  -- for an example.
  traverse f = fmap fromViewT . T.traverse (T.traverse f) . toViewT

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
hoistPre f (SeqT s) = SeqT $ fmap (f . myliftM go) s
  where
    go Empty = Empty
    go (a :< as) = a :< hoistPre f as

-- | A version of `hoist` that uses the `Monad` instance for @n@
-- rather than for @m@. Like @hoist@, the passed function is required
-- to be a monad morphism.
hoistPost :: Monad n => (forall x. m x -> n x) -> SeqT m a -> SeqT n a
hoistPost f (SeqT s) = SeqT $ fmap (myliftM go . f) s
  where
      go Empty = Empty
      go (a :< as) = a :< hoistPost f as

-- | A version of 'hoist' that works for arbitrary functions, rather
-- than just monad morphisms.
hoistPreUnexposed :: forall m n a. Monad m => (forall x. m x -> n x) -> SeqT m a -> SeqT n a
hoistPreUnexposed f (toViewT -> m) = fromViewT $ f (myliftM go m)
  where
      go Empty = Empty
      go (a :< as) = a :< hoistPreUnexposed f as

-- | A version of 'hoistPost' that works for arbitrary functions, rather
-- than just monad morphisms. This should be preferred when the `Monad` instance
-- for `n` is less expensive than that for `m`.
hoistPostUnexposed :: forall m n a. (Monad m, Monad n) => (forall x. m x -> n x) -> SeqT m a -> SeqT n a
hoistPostUnexposed f (toViewT -> m) = fromViewT $ myliftM go (f m)
  where
      go Empty = Empty
      go (a :< as) = a :< hoistPostUnexposed f as

instance MonadIO m => MonadIO (SeqT m) where
  {-# INLINE liftIO #-}
  liftIO = lift . liftIO

instance MonadReader e m => MonadReader e (SeqT m) where
  -- TODO: write more thorough tests for this instance (issue #31)
  ask = lift ask
  local f (SeqT q) = SeqT $ fmap (local f . myliftM go) q
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
  catchError (toViewT -> m) h = fromViewT $ (myliftM go m) `catchError` (toViewT . h)
    where
      go Empty = Empty
      go (a :< s) = a :< catchError s h

#if MIN_VERSION_base(4,8,0)
instance MonadZip m => MonadZip (SeqT m) where
  mzipWith f (toViewT -> m) (toViewT -> n) = fromViewT $
    mzipWith go m n
    where
      go (a :< as) (b :< bs) = f a b :< mzipWith f as bs
      go _ _ = Empty

  munzip (toViewT -> m)
    | (l, r) <- munzip (fmap go m) = (fromViewT l, fromViewT r)
    where
      go Empty = (Empty, Empty)
      go ((a, b) :< asbs) = (a :< as, b :< bs)
        where
          -- We want to be lazy so we don't force the entire
          -- structure unnecessarily. But we don't want to introduce
          -- a space leak, so we're careful to create selector thunks
          -- to deconstruct the rest of the chain.
          {-# NOINLINE muabs #-}
          {-# NOINLINE as #-}
          {-# NOINLINE bs #-}
          muabs = munzip asbs
          (as, bs) = muabs
#endif

#if MIN_VERSION_base(4,8,0)
myliftM :: Functor m => (a -> b) -> m a -> m b
myliftM = fmap
#else
myliftM :: Monad m => (a -> b) -> m a -> m b
myliftM = Monad.liftM
#endif
{-# INLINE myliftM #-}

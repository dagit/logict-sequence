{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
module Control.Monad.Logic.Sequence.Compat
  ( fromSeqT
  , toLogicT
  , fromLogicT
  , observeT
  , observe ) where

import Control.Monad.Identity (Identity(..))
import Control.Monad.Logic.Sequence.Internal hiding ( observeT, observe )

#if !MIN_VERSION_base(4,13,0)
observeT :: Monad m => SeqT m a -> m a
#else
observeT :: MonadFail m => SeqT m a -> m a
#endif
observeT (toViewT -> m) = m >>= go where
  go (a :< _) = return a
  go Empty = fail "No results."
{-# INLINE observeT #-}

observe :: Seq a -> a
observe (toViewT -> m) = case runIdentity m of
  a :< _ -> a
  Empty -> error "No results."
{-# INLINE observe #-}

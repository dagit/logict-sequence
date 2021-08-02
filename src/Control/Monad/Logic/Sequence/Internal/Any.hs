{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Trustworthy #-}
#endif

-- | It's safe to coerce /to/ 'Any' as long as you don't
-- coerce back.
module Control.Monad.Logic.Sequence.Internal.Any
  ( Any
  , toAnyList
  ) where

import GHC.Exts
import Unsafe.Coerce

-- | Convert a list of anything to a list of 'Any'.
toAnyList :: [a] -> [Any]
toAnyList = unsafeCoerce

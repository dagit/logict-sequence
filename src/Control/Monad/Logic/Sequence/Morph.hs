-- |
-- This module provides functions for changing the underlying
-- monad of a 'SeqT', just like "Control.Monad.Morph".'Control.Monad.Morph.hoist'.
--
-- The functions with the word \"Pre\" in their names lean on the
-- `Monad` instance of the original monad. The ones with the word
-- \"Post\" in their names lean on the `Monad` instance of the
-- target monad. The ones with the word \"Unexposed\" in their names
-- are reasonably well-behaved when the passed function is not
-- a monad morphism (as described in the "Control.Monad.Morph" documentation).
-- The others are typically a little more efficient, but may behave
-- strangely when passed non-monad-morphisms. In particular, if @f@ is
-- not a monad morphism, and @s1 == s2@, we do not even guarantee that
-- @'hoistPre' f s1 == 'hoistPre' f s2@.
module Control.Monad.Logic.Sequence.Morph
  ( hoistPreUnexposed
  , hoistPost
  , hoistPostUnexposed
  , hoistPre
  ) where

import Control.Monad.Logic.Sequence.Internal

{-# LANGUAGE CPP #-}
#include "logict-sequence.h"

#ifdef USE_PATTERN_SYNONYMS
{-# LANGUAGE PatternSynonyms #-}
#endif

#if __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#endif

module Control.Monad.Logic.Sequence
(
#ifdef USE_PATTERN_SYNONYMS
    SeqT(MkSeqT, getSeqT)
#else
    SeqT
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
  , cons
  , consM
  , choose
  , chooseM
  , observeAllT
  , observeAll
  , observeManyT
  , observeMany
  , observeT
  , observe
  , module Control.Monad
  , module Control.Monad.Trans
)
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Logic.Sequence.Internal

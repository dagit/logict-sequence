{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 804
-- TODO: check exactly which versions this works for
#define USE_PATTERN_SYNONYMS 1
#endif
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
#ifdef USE_PATTERN_SYNONYMS
{-# LANGUAGE PatternSynonyms #-}
#endif

#ifdef USE_PATTERN_SYNONYMS
{-# LANGUAGE Trustworthy #-}
#elif __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Safe #-}
#endif

module Control.Monad.Logic.Sequence.AsUnitLoop
(   AsUnitLoop(UL)
  , getUL
)
where

import Text.Read (Read (readPrec), Lexeme (Ident), parens, prec, lexP, step)
import Data.Function (on)
#ifdef USE_PATTERN_SYNONYMS
import Unsafe.Coerce
#endif

#if !MIN_VERSION_base(4,8,0)
import Data.Monoid (Monoid(..))
#endif

#if MIN_VERSION_base(4,9,0) && !MIN_VERSION_base(4,11,0)
import Data.Semigroup (Semigroup(..))
#endif

-- | @AsUnitLoop@ should be understood as a GADT defined thus:
--
-- @
-- data AsUnitLoop a b c where
--   UL :: !a -> AsUnitLoop a () ()
-- @
--
-- To avoid wasteful indirection, it is actually implemented in a tricky way
-- using a newtype for @AsUnitLoop@ and a pattern synonym for the @UL@
-- constructor.
#ifdef USE_PATTERN_SYNONYMS
newtype AsUnitLoop a b c = UnsafeUL a
-- Key invariant: when creating a non-bottom value of type AsUnitLoop a b c, both
-- b and c must be (). If you violate this condition, demons will come out of your nose!
{-# COMPLETE UL #-}

-- This is the true meaning of AsUnitLoop; we use it to implement the UL pattern synonym.
data SafeUnitLoop a b c where
  -- WARNING: See the strictness note in mkSafeUnitLoop
  SafeUnitLoop :: !a -> SafeUnitLoop a () ()

-- | Convert an AsUnitLoop to a SafeUnitLoop, assuming the AsUnitLoop invariant.
--
-- Note: it's critical for type safety that this function be strict.
-- This strictness is enforced by the SafeUnitLoop constructor. Imagine
-- we made that constructor lazy (and didn't compensate elsewhere). Then
-- someone could write
--
-- oops :: forall x y. x :~: y
-- oops
--   | SafeUnitLoop _ <- mkSafeUnitLoop (undefined :: AsUnitLoop () x y)
--   -- or
--   | UL _ <- undefined :: AsUnitLoop () x y
--   = Refl
--
-- and break the world. We ensure that `oops` is safely _|_.
mkSafeUnitLoop :: AsUnitLoop a b c -> SafeUnitLoop a b c
mkSafeUnitLoop (UnsafeUL a) = unsafeCoerce (SafeUnitLoop a)

-- | A bidirectional pattern synonym for 'AsUnitLoop'. See the documentation
-- there.
pattern UL :: forall a b c. () => (b ~ (), c ~ ()) => a -> AsUnitLoop a b c
-- Deconstruction relies on the AsUnitLoop invariant. Construction
-- enforces it.
pattern UL a <- (mkSafeUnitLoop -> SafeUnitLoop a)
  where
    UL a = UnsafeUL a

-- | Extract an @a@ from an @'AsUnitLoop' a b c@, throwing away the type information.
--
-- This function can be useful for avoiding "untouchable" type variable errors that
-- can occur when pattern matching with `UL` in certain contexts. In GHC 9.0.1
-- and later, this function may also be be optimized better than using 'UL' for
-- the purpose.
getUL :: AsUnitLoop a b c -> a
-- Why don't we match on UL here? That used to be fine—GHC's coercion optimizer
-- would figure out that we don't need the type equalities magicked up by
-- the UL pattern synonym here, and promptly erase the unsafe coercion and
-- the optimization barrier that implies. Since 9.0.1, however, GHC has gotten
-- more careful about unsafe coercions (see Note [Implementing unsafeCoerce]
-- in https://hackage.haskell.org/package/base-4.15.0.0/docs/src/Unsafe-Coerce.html
-- for the details). This is important for type safety in some cases, but it
-- delays erasure of unsafe coercions until much later in compilation. Will
-- that hurt us here? I can't say for sure, but there's no harm in sidestepping
-- the problem.
getUL (UnsafeUL a) = a

#else  /* When we don't have pattern synonyms */
data AsUnitLoop a b c where
  UL :: !a -> AsUnitLoop a () ()

-- | Extract an @a@ from an @'AsUnitLoop' a b c@, throwing away the type information.
--
-- This function can be useful for avoiding "untouchable" type variable errors that
-- can occur when pattern matching with `UL` in certain contexts. In GHC 9.0.1
-- and later, this function may also be be optimized better than using 'UL' for
-- the purpose.
getUL :: AsUnitLoop a b c -> a
getUL (UL a) = a
#endif

-- ----------------------------
-- Instances, mostly boring
-- ----------------------------

instance Show a => Show (AsUnitLoop a b c) where
  showsPrec d ul = showParen (d > app_prec) $
      showString "UL " . showsPrec (app_prec + 1) (getUL ul)
    where app_prec = 10

instance (Read a, b ~ (), c ~ ()) => Read (AsUnitLoop a b c) where
  readPrec = parens $ prec app_prec $ do
    Ident "UL" <- lexP
    m <- step readPrec
    return (UL m)

    where app_prec = 10

-- Note: In principle, we should have this instance, either here or in semigroupoids:
--
-- instance Semigroup a => Semigroupoid (AsUnitLoop a) where
--   UL x `o` UL y = UL (x <> y)

-- The following instances probably aren't that useful, but they're
-- all pretty obvious.
instance Eq a => Eq (AsUnitLoop a b c) where
  (==) = (==) `on` getUL

instance Ord a => Ord (AsUnitLoop a b c) where
  compare = compare `on` getUL

#if MIN_VERSION_base(4,9,0)
-- | @(<>)@ is unconditionally strict in the first argument.
instance Semigroup a => Semigroup (AsUnitLoop a b c) where
  UL x <> uly = UL (x <> getUL uly)
#endif

-- | @mappend@ is unconditionally strict in the first argument.
instance (Monoid a, b ~ (), c ~ ()) => Monoid (AsUnitLoop a b c) where
  mempty = UL mempty
#if MIN_VERSION_base(4,11,0)
  mappend = (<>)
#else
  mappend (UL x) uly = UL (mappend x (getUL uly))
#endif

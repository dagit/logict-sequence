# Revision history for logict-sequence
## 0.2.0.2 -- 2022-12-06

* Some of the laziness added in fixing the laziness bug was unnecessary.
  Remove that, allowing scheduled queues to be unboxed once more.
* Improve `RULES`, inlining, etc.
* Work around a [GHC bug](https://gitlab.haskell.org/ghc/ghc/-/issues/22549)
  relating to undecidable instances.

## 0.2.0.1 -- 2022-11-23

* Fix a serious laziness bug in `<|>` and `>>=`. These were stricter than they
  should be in some cases.

## 0.2     -- 2022-11-22

* Rename things having to do with views, to enforce a consistent
  naming convention.

* Drop support for GHC versions before 7.8.

## 0.1.0.0 -- 2021-07-19

* First version. Released on an unsuspecting world.

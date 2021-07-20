# LogicT-Sequence

Provides a variant of the `LogicT` monad that should have
asymptotically better performance when frequently observing
results. This is based on the the [Reflection without Remorse
paper.](http://okmij.org/ftp/Haskell/zseq.pdf) I created this package
mainly because the code from the paper was not easy to use as a
library.

Please see the [LogicT paper](http://okmij.org/ftp/papers/LogicT.pdf)
for examples on how to use this monad.
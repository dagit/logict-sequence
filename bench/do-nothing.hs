-- | Fallback "empty benchmark" program
module Main where

import System.IO
import System.Exit (exitFailure)

-- System.Exit.die was not implemented until 4.8 (bundled with GHC-7.10)
die :: String -> IO a
die err = hPutStrLn stderr err >> exitFailure

main :: IO ()
main = die "The benchmark suite does not support the compiler being used"


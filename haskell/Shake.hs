module  Main (main) where

import Development.Shake
import System.FilePath

main :: IO ()
main = shake shakeOptions $ do
    want ["Test.vo"]

    "*.vo" %> \out -> do
        let src = out -<.> "v"
        needed [src]
        cmd "coqc" src "-Q . Logic"

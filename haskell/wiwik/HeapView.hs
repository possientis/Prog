{-# LANGUAGE MagicHash #-}

import GHC.Exts
import GHC.HeapView
import System.Mem

main :: IO ()
main = do
    -- Constr
    clo <- getClosureData $! ([1,2,3] :: [Int])
    print clo

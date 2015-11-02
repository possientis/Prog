import Control.Monad
import System.Directory

odds :: [Integer] -> [Integer]
odds [] = []
odds (x:xs) | odd x     = x:odds xs
            | otherwise = odds xs

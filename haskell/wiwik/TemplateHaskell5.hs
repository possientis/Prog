{-# LANGUAGE TemplateHaskell #-}

import TemplateHaskell4

spliceF
spliceG "argument"

main = do
    print $ f 1 2
    print $ g ()

{-# LANGUAGE QuasiQuotes #-}

import Quasiquotation


a :: Expr
a = [calc|true|]

b :: Expr
b = [calc|succ (succ 0)|]


c :: Expr
c = [calc|pred (succ 0)|]

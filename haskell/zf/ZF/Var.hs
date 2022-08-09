module ZF.Var
  ( Var (..)
  ,x,y,z,p,q
  ) where

newtype Var = Var { unVar :: Integer }

x :: Var
x  = Var 0

y :: Var
y = Var 1

z :: Var 
z = Var 2

p :: Var 
p = Var 0

q :: Var 
q = Var 1

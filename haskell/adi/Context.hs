module  Context
    (   Context (..)
    ,   Binding (..)
    ,   c0, c1, c2
    ,   (>>>)
    )   where

import Var
import EType

infix 8 :~>

data Binding = Var :~> EType 

infixl 7 :::
data Context = O | Context ::: Binding

x :: Var
x = mkVar "x"

y :: Var
y = mkVar "y"

c0 :: Context
c0 = O 

c1 :: Context
c1 = O ::: x :~> TNat

c2 :: Context
c2 = O ::: x :~> TNat ::: y :~> TNat :-> TNat :-> TNat


infix 6 >>>
(>>>) :: Context -> Var -> Maybe EType
(>>>) O _ = Nothing
(>>>) (ctx ::: (m :~> s)) n = if n == m then Just s else ctx >>> n
    


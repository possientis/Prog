module  Literal
    (   Literal     (..)
    ,   tiLit
    )   where

import TI
import Syntax
import TypeClass

data Literal
    = LitInt  Integer
    | LitChar Char
    | LitRat  Rational
    | LitStr  String


tiLit :: Literal -> TI ([Pred], Type)
tiLit (LitChar _) = return ([], tChar)
tiLit (LitInt  _) = do { v <- newTVar Star; return ([IsIn "Num" v], v) }
tiLit (LitStr  _) = return ([], tString)
tiLit (LitRat  _) = do { v <- newTVar Star; return ([IsIn "Fractional" v], v) }

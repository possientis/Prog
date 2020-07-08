module  Macro
    (   eSum
    ,   eFac
    )   where

import Op
import Syntax

-- \x y -> x + y
eSum :: String -> String -> Expr
eSum x y = 
    (eLam x
        (eLam y
            (eOp oAdd [(eVar x),(eVar y)])))

eFac :: String -> String -> Expr
eFac f n =
    (eRec f
       (eLam n
            (eIf (eVar n) (eNum 1) 
                (eOp oMul 
                    [(eVar n) 
                    ,(eApp (eVar f) 
                        (eOp oAdd [(eVar n), (eNum (-1))] ))
                    ])))) 

module  Alternative
    (   Alt
    ,   tiAlt
    ,   tiAlts
    )   where

import TI
import Expr
import Infer
import Syntax
import Pattern
import TypeClass
import Assumption

type Alt = ([Pat], Expr)


tiAlt :: Infer Alt Type
tiAlt ce as (pats, e) = do 
    (ps, as', ts) <- tiPats pats
    (qs, t)       <- tiExpr ce (as' ++ as) e
    return (ps ++ qs, foldr fn t ts)


tiAlts :: ClassEnv -> [Assump] -> [Alt] -> Type -> TI [Pred]
tiAlts ce as alts t = do
    psts <- mapM (tiAlt ce as) alts
    _    <- mapM (unify t) (map snd psts)
    return (concat (map fst psts)) 

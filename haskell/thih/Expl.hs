module  Expl    -- Explicitly typed bindings
    (   Expl
    ,   tiExpl
    )   where

import Data.List

import TI
import Split
import Subst
import Syntax
import Scheme
import TypeClass
import Assumption
import Alternative

type Expl = (Id, Scheme, [Alt])

tiExpl :: ClassEnv -> [Assump] -> Expl -> TI [Pred]
tiExpl ce as (_,sc,alts) = do
    (qs :=> t) <- freshInst sc
    ps         <- tiAlts ce as alts t
    s          <- getSubst
    let qs'    = apply s qs
        t'     = apply s t
        fs     = tv (apply s as)
        gs     = tv t' \\ fs
        sc'    = quantify gs (qs' :=> t')
        ps'    = filter (not . entail ce qs') (apply s ps)
    (ds, rs)   <- split ce fs gs ps'
    if sc /= sc'
        then fail "signature too general"
        else if not (null rs) 
            then fail "context too weak"
            else return ds







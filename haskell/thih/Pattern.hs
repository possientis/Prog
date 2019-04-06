module  Pattern
    (   Pat     (..)
    ,   tiPat
    )   where

import TI
import Scheme
import Syntax
import Literal
import Assumption
import TypeClass

data Pat 
    = PVar Id               -- (i) 
    | PWildcard             -- (ii) 
    | PAs Id Pat            -- (iii) 
    | PLit Literal          -- (iv)
    | PNpk Id Integer       -- (v)
    | PCon Assump [Pat]     -- (vi)

{-
 - (i)  A 'PVar i' pattern matches any value and binds it to the variable i.
 - (ii) A 'PWildcard' pattern ('_' in Haskell) matches any value, but no binding. 
 - (iii)A 'PAs i pat' ('i@pat' in Haskell) matches any value that matches 
 - the pattern pat, and binds it to the variable i, while also binding any 
 - variable that appears in pat.
 - (iv) A 'PLit l' pattern only matches the value denoted by l with no binding 
 - (v)  A 'PNpk i k' pattern known as an 'n+k' pattern in Haskell, matches
 - any positive integral value m that is greater than or equal to k, and 
 - binds the variable i to the difference m - k.
 - (vi) A 'PCon a pats' pattern matches only values that were built
 - using the constructor function a with a sequence of arguments 
 - that matches pats. We use values a of type Assump to represent 
 - constructor functions. All that we need for typechecking is the
 - type, although the name is useful for debugging
 -}

tiPat :: Pat -> TI ([Pred], [Assump], Type)

tiPat (PVar i)      = do { v <- newTVar Star; return ([],[i:>:toScheme v], v) }
tiPat (PWildcard)   = do { v <- newTVar Star; return ([],[],v) }
tiPat (PLit l)      = do { (ps, t) <- tiLit l; return (ps, [], t) }

tiPat (PAs i pat)   = do
    (ps, as, t) <- tiPat pat 
    return (ps, (i:>:toScheme t):as, t)

tiPat (PNpk i _)    = do 
    t <- newTVar Star
    return ([IsIn "Integral" t],[i:>:toScheme t],t)

tiPat (PCon (_:>:sc) pats) = do
    (ps,as,ts) <- tiPats pats
    t'         <- newTVar Star
    (qs :=> t) <- freshInst sc 
    unify t (foldr fn t' ts)
    return $ (ps ++ qs, as, t')  

tiPats :: [Pat] -> TI ([Pred], [Assump], [Type])
tiPats pats = do
    psasts <- mapM tiPat pats
    let ps = concat [ps' | (ps',_,_) <- psasts ]
        as = concat [as' | (_,as',_) <- psasts ]
        ts =        [t   | (_,_,t)   <- psasts ]
    return (ps,as,ts) 



module  Impl    -- Implicitly typed bindings
    (   Impl
    ,   tiImpls
    )   where

import Data.List

import TI
import Infer
import Split
import Subst
import Syntax
import Scheme
import TypeClass
import Assumption
import Alternative


type Impl = (Id, [Alt])

restricted :: [Impl] -> Bool
restricted bs = any simple bs where
    simple (_,alts) = any (null . fst) alts

tiImpls :: Infer [Impl] [Assump]
tiImpls ce as bs = do
    ts  <- mapM (\_ -> newTVar Star) bs
    let is      = map fst bs
        scs     = map toScheme ts
        as'     = zipWith (:>:) is scs ++ as
        altss   = map snd bs
    pss <- sequence (zipWith (tiAlts ce as') altss ts)
    s   <- getSubst
    let ps'     = apply s (concat pss)
        ts'     = apply s ts
        fs      = tv (apply s as)
        vss     = map tv ts'
        gs      = foldr1 union  vss \\ fs
    (ds, rs)   <- split ce fs (foldr1 intersect vss) ps'
    if restricted bs 
        then 
            let gs' = gs \\ tv rs
                scs'= map (quantify gs' . ([] :=>)) ts'
            in return (ds ++ rs, zipWith (:>:) is scs')
        else
            let scs' = map (quantify gs . (rs :=>)) ts'
            in return (ds, zipWith (:>:) is scs') 


module  Split
    (   split
    )   where

import Data.List
 
import Subst
import Syntax
import Default
import TypeClass

split :: Monad m => ClassEnv -> [Tyvar] -> [Tyvar] -> [Pred] -> m ([Pred],[Pred])
split ce fs gs ps = do
    ps' <- reduce ce ps
    let (ds, rs) = partition (all (`elem` fs) . tv) ps'
    rs' <- defaultedPreds ce (fs ++ gs) rs
    return (ds, rs \\ rs') 

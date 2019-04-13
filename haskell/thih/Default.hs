module  Default
    (   defaultedPreds
    ,   Ambiguity 
    ,   ambiguities
    ,   defaultSubst
    )   where

import Data.List

import Subst
import Syntax
import TypeClass

type Ambiguity = (Tyvar, [Pred])

ambiguities :: ClassEnv -> [Tyvar] -> [Pred] -> [Ambiguity]
ambiguities _ vs ps = [(v,filter (elem v . tv) ps) | v <- tv ps \\ vs ]


numClasses :: [Id]
numClasses =  ["Num"
              ,"Integral"
              ,"Floating"
              ,"Fractional"
              ,"Real"
              ,"RealFloat"
              ,"RealFrac"
              ]


stdClasses :: [Id]
stdClasses =  ["Eq"
              ,"Ord"
              ,"Show"
              ,"Read"
              ,"Bounded"
              ,"Enum"
              ,"Ix"
              ,"Functor"
              ,"Applicative"
              ,"Monad"
              ,"MonadPlus"
              ] ++ numClasses

candidates :: ClassEnv -> Ambiguity -> [Type]
candidates ce (v,qs) =  [t'  
                        | let is = [i | IsIn i _ <- qs]
                              ts = [t | IsIn _ t <- qs]
                        , all ((TVar v) ==) ts
                        , any (`elem` numClasses) is
                        , all (`elem` stdClasses) is
                        , t' <- defaults ce
                        , all (entail ce []) [IsIn i t' | i <- is]
                        ]
                            
withDefaults :: Monad m 
             => ([Ambiguity] -> [Type] -> a) 
             -> ClassEnv
             -> [Tyvar]
             -> [Pred]
             -> m a

withDefaults f ce vs ps
    | any null tss  = fail "cannot resolve ambiguity"
    | otherwise     = return (f vps (map head tss))
    where
    vps = ambiguities ce vs ps
    tss = map (candidates ce) vps

defaultedPreds :: Monad m => ClassEnv -> [Tyvar] -> [Pred] -> m [Pred]
defaultedPreds = withDefaults (\vps _ -> concat (map snd vps))

defaultSubst :: Monad m => ClassEnv -> [Tyvar] -> [Pred] -> m Subst
defaultSubst = withDefaults (\vps ts -> zip (map fst vps) ts)





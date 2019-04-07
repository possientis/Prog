module  Default
    (   defaultedPreds
    ,   Ambiguity 
    ,   ambiguities
    )   where

import Data.List

import Subst
import Syntax
import TypeClass

type Ambiguity = (Tyvar, [Pred])

defaultedPreds :: Monad m => ClassEnv -> [Tyvar] -> [Pred] -> m [Pred]
defaultedPreds = undefined  -- TBD

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
                            


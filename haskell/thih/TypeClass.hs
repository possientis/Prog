module  TypeClass
    (   q1
    )   where

import Syntax

data Pred = IsIn Id Type deriving Eq

data Qual t = [Pred] :=> t deriving Eq

-- a -> Int
t1 :: Type
t1 = TVar (Tyvar "a" Star) `fn` tInt

-- (Num a) => a -> Int
q1 :: Qual Type
q1 = [IsIn "Num" (TVar (Tyvar "a" Star))] :=> t1



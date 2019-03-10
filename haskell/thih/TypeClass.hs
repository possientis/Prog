module  TypeClass
    (   q1
    ,   ord
    ,   mguPred
    ,   matchPred
    ,   Inst
    ,   Class
    )   where

import Subst
import Syntax

import Data.List

data Pred = IsIn Id Type deriving Eq

data Qual t = [Pred] :=> t deriving Eq

-- a -> Int
t1 :: Type
t1 = TVar (Tyvar "a" Star) `fn` tInt

-- (Num a) => a -> Int
q1 :: Qual Type
q1 = [IsIn "Num" (TVar (Tyvar "a" Star))] :=> t1

instance Types Pred where
    apply s (IsIn i t)   = IsIn i (apply s t)
    tv (IsIn _ t)        = tv t

instance (Types t) => Types (Qual t) where
    apply s (ps :=> t)  = apply s ps :=> apply s t
    tv (ps :=> t)       = tv ps `union` tv t

lift :: (Monad m) => (Type -> Type -> m Subst) -> Pred -> Pred -> m Subst
lift m (IsIn i t) (IsIn i' t')
    | i == i'       = m t t'
    | otherwise     = fail "lift: classes differ" 

mguPred :: (Monad m) => Pred -> Pred -> m Subst
mguPred = lift mgu

matchPred :: (Monad m) => Pred -> Pred -> m Subst
matchPred = lift match

-- So an instance is a list of predicates, and a predicate ?
type Inst = Qual Pred

-- A Class is a pair of lists: 
-- 1. list of superclass 2. entry for each instance declaration
type Class = ([Id],[Inst])

-- class Eq a => Ord a where ... (Eq is a superclass of Ord)
-- instance Ord () where ...
-- instance Ord Char where ...
-- instance Ord Int where
-- instance (Ord a, Ord b) => Ord (a, b) where ...
ord :: Class
ord = ( ["Eq"]
      , [ [] :=> IsIn "Ord" tUnit
        , [] :=> IsIn "Ord" tChar
        , [] :=> IsIn "Ord" tInt
        , [ IsIn "Ord" (TVar (Tyvar "a" Star))
          , IsIn "Ord" (TVar (Tyvar "b" Star))
          ]  :=> IsIn "Ord" 
                ( pair  (TVar (Tyvar "a" Star)) 
                        (TVar (Tyvar "b" Star))
                ) 
        ]
      )




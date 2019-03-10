module  Subst
    (   Subst
    ,   Types   (..)
    ,   nullSubst
    ,   merge
    ,   (@@)
    ,   (+->)
    ,   mgu
    ,   match
    )   where

import Syntax

import Data.List


type Subst = [(Tyvar, Type)]

nullSubst :: Subst
nullSubst = []


(+->) :: Tyvar -> Type -> Subst
(+->) u t = [(u,t)]

class Types t where
    apply :: Subst -> t -> t
    tv    :: t -> [Tyvar]


instance Types Type where
    apply s (TVar u)  = case lookup u s of { Just t  -> t ; Nothing -> TVar u }
    apply s (TAp l r) = TAp (apply s l) (apply s r)
    apply _ (TCon c)  = TCon c 
    apply _ (TGen _)  = error "apply: TGen type is not yet supported"

    tv (TVar u)       = [u]
    tv (TAp l r)      = tv l `union` tv r
    tv (TCon _)       = []
    tv (TGen _)       = error "tv: TGen type is not yet supported" 

instance Types a => Types [a] where
    apply s = map (apply s)
    tv      = nub . concat . map tv


infixr 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = [(u, apply s1 t) | (u,t) <- s2] ++ s1


merge :: Monad m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return (s1 ++ s2) else fail "merge fails"
    where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v)) 
            (map fst s1 `intersect` map fst s2)

-- Definition: A 'substition' s is a unifier of two types t1 and t2 
-- iff apply s t1 == apply s t2. A 'most general unifier' of t1 t2
-- is a unifier u with the property that any other unifier s can be
-- wrtitten as s == s' @@ u for some substitution s'.

mgu :: (Monad m) => Type -> Type -> m Subst
mgu (TAp l r) (TAp l' r')   = do
    s1 <- mgu l l'
    s2 <- mgu (apply s1 r) (apply s1 r')
    return (s2 @@ s1)
mgu (TVar u) t              = varBind u t
mgu t (TVar u)              = varBind u t
mgu (TCon tc1) (TCon tc2)
    | tc1 == tc2            = return nullSubst
mgu _ _                     = fail "types do not unify"

varBind :: (Monad m) => Tyvar -> Type -> m Subst
varBind u t
    | t == TVar u       = return nullSubst
    | u `elem` tv t     = fail "occurs check fails"
    | kind u /= kind t  = fail "kinds do not match"
    | otherwise         = return (u +-> t)


match :: Monad m => Type -> Type -> m Subst
match (TAp l r ) (TAp l' r')    = do
    sl <- match l l'
    sr <- match r r'
    merge sl sr 
match (TVar u) t
    | kind u == kind t          = return (u +-> t)
match (TCon tc1) (TCon tc2)
    | tc1 == tc2                = return nullSubst
match _ _                       = fail "match: types do not match"

module  TI
    (   TI  (..)
    ,   runTI
    ,   getSubst
    ,   unify
    ,   newTVar
    ,   freshInst
    )   where

import Subst
import Scheme
import Syntax
import TypeClass

-- The 'TI' (Type Inference) monad is a state monad where the state
-- is simply a substitution (the current substitution) and an integer
-- (needed for generating fresh variables)

newtype TI a = TI { unTI :: Subst -> Int -> (Subst, Int, a) }

instance Functor TI where
    fmap f m = TI $ \s i -> let (s',i',a) = unTI m s i  in (s',i',f a)

instance Applicative TI where
    pure      = return
    (<*>) g m = g >>= \f -> fmap f m 

instance Monad TI where
    return a  = TI $ \s i -> (s, i, a) 
    m >>= f   = TI $ \s i -> let (s',i',a) = unTI m s i in unTI (f a) s' i'

runTI :: TI a -> a
runTI m = let (_,_,x) = unTI m nullSubst 0 in x


getSubst :: TI Subst
getSubst = TI (\s n -> (s,n,s))

extSubst :: Subst -> TI ()
extSubst s' = TI (\s n -> (s'@@s,n,()))

unify :: Type -> Type -> TI ()
unify t1 t2 = do
    s <- getSubst
    u <- mgu (apply s t1) (apply s t2)
    extSubst u

newTVar :: Kind -> TI Type
newTVar k = TI (\s n -> let v = Tyvar (enumId n) k in (s,n+1,TVar v))

freshInst :: Scheme -> TI (Qual Type)
freshInst (Forall ks qt) = do
    ts <- mapM newTVar ks
    return (inst ts qt)
{-
 - The definition relies on an auxiliary function inst, which is a variation 
 - of apply that works on generic variables. In other words, inst ts t replaces 
 - each occurrence of a generic variable TGen n in t with ts !! n. It is 
 - convenient to build up the definition of inst using overloading
-}

class Instantiate t where
    inst :: [Type] -> t -> t

instance Instantiate Type where
    inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
    inst ts (TGen n)  = ts !! n
    inst _ t         = t

instance Instantiate a => Instantiate [a] where
    inst ts = map (inst ts)

instance Instantiate t => Instantiate (Qual t) where
    inst ts (ps :=> t) = inst ts ps :=> inst ts t

instance Instantiate Pred where
    inst ts (IsIn c t) = IsIn c (inst ts t)



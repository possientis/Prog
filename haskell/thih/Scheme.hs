module  Scheme
    (   Scheme 
    ,   quantify
    )   where

import Subst
import Syntax
import TypeClass

data Scheme = Forall [Kind] (Qual Type) 
    deriving Eq

instance Types Scheme where
    apply s (Forall ks qt) = Forall ks (apply s qt)
    tv (Forall _ qt)      = tv qt


quantify :: [Tyvar] -> Qual Type -> Scheme
quantify vs qt = Forall ks (apply s qt)
    where   vs' = [v| v <- tv qt, v `elem` vs]
            ks  = map kind vs'
            s   = zip vs' (map TGen [0..]) 


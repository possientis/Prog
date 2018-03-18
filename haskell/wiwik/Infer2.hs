{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}



module Infer2 where

import GHC.Generics
import Data.Typeable (Typeable)
import Data.Set as S

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

data Exp 
    = Var (Name Exp)
    | Lam (Bind (Name Exp) Exp)
    | App Exp Exp
    deriving (Show, Generic, Typeable) 


instance Alpha Exp

instance Subst Exp Exp where
    isvar (Var x)   = Just (SubstName x)
    isvar _         = Nothing

fvSet :: (Alpha a, Typeable b) => a -> S.Set (Name b)
fvSet = S.fromList . toListOf fv

type M a = FreshM a

(=~) :: Exp -> Exp -> M Bool
e1 =~ e2 | e1 `aeq` e2  = return True
e1 =~ e2 = do
    e1' <- red e1
    e2' <- red e2
    if e1' `aeq` e1 && e2' `aeq` e2
        then return False
        else e1' =~ e2'

-- Reduction
red :: Exp -> M Exp
red (App e1 e2) = do
    e1' <- red e1
    e2' <- red e2
    case e1' of
        Lam bnd -> do
            (x,e1'') <- unbind bnd
            return $ subst x e2' e1''

        otherwise -> return $ App e1' e2'
red (Lam bnd) = do
    (x,e) <- unbind bnd
    e' <- red e
    case e of
        App e1 (Var y) | y == x && x `S.notMember` fvSet e1 -> return e1
        otherwise -> return (Lam (bind x e'))
red (Var x) = return $ (Var x)

 



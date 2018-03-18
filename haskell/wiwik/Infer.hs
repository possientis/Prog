-- Hindley-Milner 
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}


module Infer where

import Data.String
import Control.Monad.Error

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Unbound.LocallyNameless as NL
import Unbound.LocallyNameless hiding (Subst, compose)


data Type 
    = TVar (Name Type)
    | TArr Type Type
    deriving (Show)


data Expr 
    = Var (Name Expr)
    | Lam (Bind (Name Expr) Expr)
    | App Expr Expr
    | Let (Bind (Name Expr) Expr)
    deriving (Show)


$(derive [''Type, ''Expr])


instance IsString Expr where
    fromString = Var . fromString

instance IsString (Name Expr) where
    fromString = string2Name

instance IsString Type where
    fromString = TVar . fromString

instance IsString (Name Type) where
    fromString = string2Name

eqType :: Type -> Type -> Bool
eqType (TVar v1) (TVar v2)  = v1 == v2
eqType _         _          = False


uvar :: String -> Expr
uvar s = Var (s2n s)

tvar :: String -> Type
tvar s = TVar (s2n s)

instance Alpha Type
instance Alpha Expr


instance NL.Subst Type Type where
    isvar (TVar v)  = Just (SubstName v)
    isvar _         = Nothing

instance NL.Subst Expr Expr where
    isvar (Var v)   = Just (SubstName v)
    isvar _         = Nothing
 
instance NL.Subst Expr Type where

data TypeError
    = UnboundVariable (Name Expr)
    | GenericTypeError 
    deriving (Show)


instance Error TypeError where
    noMsg = GenericTypeError

type Env = Map (Name Expr) Type
type Constraint = (Type, Type)
type Infer = ErrorT TypeError FreshM

empty :: Env
empty = Map.empty

freshtv :: Infer Type
freshtv = do
    x <- fresh "_t"
    return $ TVar x

instance Fresh Infer where
    fresh = do 
    x <- fresh 
    return x

infer :: Env -> Expr -> Infer (Type, [Constraint])
infer env expr = case expr of
    
    Lam b -> do
        (n, e)  <- unbind b
        tv      <- freshtv
        let env' = Map.insert n tv env
        (t, cs) <- infer env' e 
        return (TArr tv t, cs)

    App e1 e2 -> do
        (t1, cs1) <- infer env e1
        (t2, cs2) <- infer env e2
        tv <- freshtv
        return (tv, (t1, TArr t2 tv) : cs1 ++ cs2)

    Var n -> do
        case Map.lookup n env of
            Nothing -> throwError $ UnboundVariable n
            Just t  -> return (t, [])

    Let b -> do
        (n, e) <- unbind b
        (tBody, csBody) <- infer env e
        let env' = Map.insert n tBody env
        (t, cs) <- infer env e
        return (t, cs ++ csBody) 


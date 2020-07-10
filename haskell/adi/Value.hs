{-# LANGUAGE LambdaCase     #-}

module  Value
    (   Value
    ,   mkNil
    ,   mkNum
    ,   mkBool
    ,   mkClo
    ,   mkNat
    ,   num
    ,   bool
    ,   nat
    ,   closure
    ,   delta
    )   where

import Op
import Var
import Env
import Syntax
import Closure

import Data.Functor.Identity

data Value 
    = Nil 
    | Num  Integer
    | Bool Bool
    | Clo  Closure
    | Nat Integer

instance Show Value where
    show = \case 
        Nil     -> "<nil>"
        Num  n  -> show n
        Bool b  -> show b
        Clo  c  -> show c
        Nat  n  -> show n

delta :: Op -> [Value] -> Value
delta op args = case checkArgs args of
    Left err    -> error $ "Error: " ++ show op ++ ": " ++ err
    Right pvs   -> mkValue $ deltaPrim op pvs

checkArgs :: [Value] -> Either String [PrimValue]
checkArgs = mapM checkArg

checkArg :: Value -> Either String PrimValue
checkArg v = case v of
    Nil     -> Left $ "Nil argument encountered in primitive call"
    Clo c   -> Left $ "Closure encountered in primitive call: " ++ show c
    Num n   -> Right . PNum  . Identity $ n
    Bool b  -> Right . PBool . Identity $ b
    Nat  n  -> Left $ "Nat encountered in primitive call: " ++ show n

mkValue :: PrimValue -> Value
mkValue = \case
    PNum (Identity n)  -> Num n
    PBool (Identity b) -> Bool b
    
num :: Value -> Maybe Integer
num = \case
    Num n   -> Just n
    _       -> Nothing

bool :: Value -> Maybe Bool
bool = \case
    Bool b  -> Just b
    _       -> Nothing

nat :: Value -> Maybe Integer
nat = \case
    Nat n   -> Just n
    _       -> Nothing

closure :: Value -> Maybe Closure
closure = \case
    Clo c   -> Just c
    _       -> Nothing

mkNil :: Value 
mkNil = Nil

mkNum :: Integer -> Value
mkNum = Num

mkBool :: Bool -> Value
mkBool = Bool

mkNat :: Integer -> Value
mkNat n
    | n < 0     = error "mkNat : illegal argument, cannot be negative"
    | otherwise = Nat n

mkClo :: Var -> Expr -> Env -> Value
mkClo x e env = Clo $ mkClosure x e env



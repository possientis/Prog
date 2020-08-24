{-# LANGUAGE LambdaCase     #-}

module  Value
    (   Value
    ,   mkNil
    ,   mkNum
    ,   mkBool
    ,   mkClo
    ,   mkZero
    ,   mkSuc
    ,   num
    ,   bool
    ,   bool'
    ,   closure
    ,   delta
    ,   isZero
    ,   suc
    ,   toInt
    ,   nat
    )   where

import Op
import Var
import Env
import Error
import Syntax
import Closure

import Data.Functor.Identity

data Value 
    = Nil 
    | Num  Integer
    | Bool Bool
    | Clo  Closure
    | Zero
    | Suc Value

instance Show Value where
    show v = case v of 
        Nil     -> "<nil>"
        Num  n  -> show n
        Bool b  -> show b
        Clo  c  -> show c
        Zero    -> "zero"
        Suc _   -> maybe "???" show (toInt' v)

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
    Zero    -> Left $ "Nat zero encountered in primitive call"
    Suc _   -> Left $ "Nat encountered in primitive call: " ++ show v

mkValue :: PrimValue -> Value
mkValue = \case
    PNum (Identity n)  -> Num n
    PBool (Identity b) -> Bool b
    
num :: Either Error Value -> Maybe Integer
num = \case
    Left _  -> Nothing
    Right v -> case v of
        Num n   -> Just n
        _       -> Nothing

bool :: Either Error Value -> Maybe Bool
bool = \case
    Left _  -> Nothing
    Right v -> case v of
        Bool b  -> Just b
        _       -> Nothing

bool' :: Value -> Maybe Bool
bool' = \case
    Bool b  -> Just b
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

mkZero :: Value
mkZero = Zero

mkSuc :: Value -> Value
mkSuc = Suc

mkClo :: Var -> Expr -> Env -> Value
mkClo x e env = Clo $ mkClosure x e env

toInt :: Either Error Value -> Maybe Integer
toInt = \case
    Left _    -> Nothing
    Right val -> case val of
        Zero  -> Just 0
        Suc v -> (+1) <$> toInt' v
        _     -> Nothing

toInt' :: Value -> Maybe Integer
toInt' = \case
    Zero  -> Just 0
    Suc v -> (+1) <$> toInt' v
    _     -> Nothing


isZero :: Value -> Bool
isZero = \case
    Zero -> True
    _    -> False

suc :: Value -> Maybe Value
suc = \case
    Suc v   -> Just v
    _       -> Nothing

nat :: Value -> Maybe Value
nat = \case 
    Zero    -> Just Zero
    Suc v   -> Suc <$> nat v
    _       -> Nothing

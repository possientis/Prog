{-# LANGUAGE DeriveDataTypeable #-}

import Data.Data
import Data.Typeable
import Data.Generics.Uniplate.Direct

data Expr a
    = Fls
    | Tru
    | Var a
    | Not (Expr a)
    | And (Expr a) (Expr a)
    | Or  (Expr a) (Expr a)
    deriving (Data, Typeable, Show,Eq)



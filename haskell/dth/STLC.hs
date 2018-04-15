{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

data Ty = Unit | Ty :~> Ty

infixr 0 :~>


data Elem :: [k] -> k -> * where
    EZ :: Elem (x ': xs) x
    ES :: Elem xs x -> Elem (y ': xs) x

data Expr :: [Ty] -> Ty -> * where
    Var :: Elem ctx ty                              -> Expr ctx ty
    Lam :: Expr (arg ': ctx) res                    -> Expr ctx (arg ':~> res)
    App :: Expr ctx (arg ':~> res) -> Expr ctx arg  -> Expr ctx res
    TT  ::                                             Expr ctx 'Unit


data Val :: Ty -> * where 
    LamVal :: Expr '[arg] res -> Val (arg ':~> res)
    TTVal  ::                    Val 'Unit     


eval :: Expr '[] ty -> Val ty
eval = undefined


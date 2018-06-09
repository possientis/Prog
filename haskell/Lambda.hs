newtype D = D { unD :: D -> D }

ex1 :: D 
ex1 =  D id

ex2 :: D
ex2 =  D (const ex1)

lam :: (D -> D) -> D 
lam = D

ap :: D -> D -> D
ap (D f) x = f x


newtype Var = Var Int

data Lam
    = LVar Var
    | LLam Var Lam
    | LApp Lam Lam



data K = Top | Arr K K | Prod K K 















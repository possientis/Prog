type Name = String

data Exp
    = Var Name
    | Lam Name Exp
    | App Exp Exp


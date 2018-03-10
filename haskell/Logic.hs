data Expr v = In v v
            | Bot
            | Imply (Expr v) (Expr v)
            | Forall v (Expr v)

axiom :: Expr v -> Bool
axiom = undefined

data Proof v    = Axiom (Expr v)
                | Hypothesis (Expr v)
                | ModusPonens (Proof v) (Proof v)
                | Generalization v (Proof v) 

eval :: Proof v -> Expr v
eval (Axiom p) | axiom p    = p
eval (Hypothesis p)         = p 

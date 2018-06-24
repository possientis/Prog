Require Import term.
(* substituting the term t1 for the variable x in t *)
Fixpoint subst (x:Var) (t1:Term) (t:Term) : Term :=
    match t with
    | VarTerm y     =>  if varEqual x y then t1 else t  
    | AbsTerm y t2  => (* how to avoid variable capture ? *)   

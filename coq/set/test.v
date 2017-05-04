Set Implicit Arguments.

CoInductive list(A:Set) : Set :=
  | cons: A -> list A -> list A.

Variable V: Set.
Variable f: V -> V.
Variable a: V.

CoFixpoint from (v:V) : list V  := cons v (from (f v)). 
  

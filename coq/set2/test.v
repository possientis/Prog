Set Implicit Arguments.

CoInductive list(A:Set) : Set :=
  | cons: A -> list A -> list A.

Parameter V: Set.
Parameter f: V -> V.
Parameter a: V.

CoFixpoint from (v:V) : list V  := cons v (from (f v)).


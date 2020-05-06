Require Utils.Nub.

Require Import Core.Set.
Require Import Core.Leq.

(* eliminates syntactic duplicates, not semantics duplicates                    *)
Definition nub (x:set) : set := fromList (Nub.nub (toList x)). 

Definition Nubed (x:set) : Prop := Nub.Nubed (toList x).

    

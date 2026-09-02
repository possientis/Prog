Require Import List.

Require Import Logic.Prop.Syntax.

Declare Scope Prop_Context_scope.

(* A context is a list of propositions. No need to create a 'snoc' version for  *)
(* this, we simply need to remember new formulas are 'cons'-ed to the left      *)
Definition Ctx (v: Type) : Type := list (P v).

Notation "G ; p" := (cons p G)
  (at level 50, left associativity) : Prop_Context_scope.

Open Scope Prop_Context_scope.
 

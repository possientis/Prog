Declare Scope ZF_Set_Eval_scope.
Open    Scope ZF_Set_Eval_scope.

Require Import ZF.Class.
Require Import ZF.Class.Eval.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

Definition eval (P:Class) (a:U) : U := fromClass (Class.Eval.eval P a)
  (EvalIsSmall P a).

Notation "P :( a ):" := (eval P a)
  (at level 0, no associativity) : ZF_Set_Eval_scope.

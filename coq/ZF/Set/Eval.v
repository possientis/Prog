Require Import ZF.Class.
Require Import ZF.Class.Eval.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

Definition eval (P:Class) (a:U) : U := fromClass (Class.Eval.eval P a)
  (EvalIsSmall P a).

Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.Eval2.
Export ZF.Notation.Eval2.

(* Evaluation 'as a class' of a class F at a point i.                           *)
Definition eval (F:Class) (i:U) : Class := fun x => F :(i,x):.


(* Notation "F$i" := (eval F i)                                                 *)
Global Instance ClassEval2 : Eval2 Class U Class := { eval2 := eval }.

Proposition EquivCompat : forall (F G:Class) (i:U),
  F :~: G -> F$i :~: G$i.
Proof.
  intros F G i H1. intros x. split; intros H2; apply H1; assumption.
Qed.

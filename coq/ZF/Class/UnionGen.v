Require Import ZF.Class.Core.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.Eval.

(* Defining the generalized union \/_{x in P} Q(x).                             *)
Definition unionGen (P Q:Class) : Class
  := :U( fun y => exists x, P x /\ y = Q!x ).

Proposition UnionGenCharac : forall (P Q:Class) (y:U),
  unionGen P Q y <-> exists x, P x /\ y :< Q!x.
Proof.
  intros P Q y. split; intros H1.
  - destruct H1 as [q [H1 H2]]. destruct H2 as [x [H2 H3]].
    rewrite H3 in H1. exists x. split; assumption.
  - destruct H1 as [x [H1 H2]]. exists (eval Q x). split.
    + assumption.
    + exists x. split. { assumption. } { reflexivity. }
Qed.

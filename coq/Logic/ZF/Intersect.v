Declare Scope ZF_Intersect_scope.
Open    Scope ZF_Intersect_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Comprehension.
Require Import Logic.ZF.Extensionality.

(* The intersection of two sets a and b.                                        *)
Definition intersect (a b:U) : U := :{ a | fun x => x :< b }:.

Notation "a :/\: b" := (intersect a b)
  (at level 3, left associativity) : ZF_Intersect_scope.

Proposition IntersectCharac : forall (a b:U),
 forall x, x :< (a:/\:b) <-> x :< a /\ x :< b.
Proof.
  intros a b x. unfold intersect. split.
  - intros H. apply CompCharac in H. apply H.
  - intros [H1 H2]. apply CompCharac. auto.
Qed.

Proposition IntersectComm : forall (a b:U), a:/\:b = b:/\:a.
Proof.
  intros a b. apply Extensionality. intros x. split;
  intros H1; apply IntersectCharac; apply IntersectCharac in H1;
  destruct H1 as [H1 H2]; auto.
Qed.

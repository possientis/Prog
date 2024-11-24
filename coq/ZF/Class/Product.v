Declare Scope ZF_Class_Product_scope.
Open    Scope ZF_Class_Product_scope.

Require Import ZF.Axiom.Core.
Require Import ZF.Class.Class.
Require Import ZF.Set.OrdPair.

Definition prodClass (P Q:Class) : Class := fun x =>
  exists y, exists z, x = :(y,z): /\ P y /\ Q z.

Notation "P :x: Q" := (prodClass P Q)
  (at level 4, left associativity) : ZF_Class_Product_scope.

Proposition ProdCharac2 : forall (P Q:Class),
  forall y, forall z, P :x: Q :(y,z): <-> P y /\ Q z.
Proof.
  intros P Q y z. split; intros H1.
  - unfold prodClass in H1. destruct H1 as [y' [z' [H1 [H2 H3]]]].
    apply OrdPairEqual in H1. destruct H1 as [H1 H1']. subst. split; assumption.
  - destruct H1 as [H1 H2]. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.


Require Import ZF.Notation.Slash.
Export ZF.Notation.Slash.

(* The restriction of a class (viewed as relation) to another relation.         *)
Definition restrict (R A:Class) : Class := R :/\: (A :x: A).


(* Notation "R :/: A" := (restrict R A)                                         *)
Global Instance ClassSlash : Slash Class Class := { slash := restrict }.

(* R restricted to A at (x,y) iff x in A and y in A and R holds at (x,y).       *)
Proposition Charac2 : forall (R A:Class) (x y:U),
  (R:/:A) :(x,y): <-> A x /\ A y /\ R :(x,y):.
Proof.
  intros R A x y. split; intros H1.
  - destruct H1 as [H1 H2]. apply Prod.Charac2 in H2. destruct H2 as [H2 H3].
    split. 1: assumption. split; assumption.
  - split. 1: apply H1. apply Prod.Charac2. split; apply H1.
Qed.

(* The restriction of a class to A is a relation.                               *)
Proposition IsRelation : forall (R A:Class), Relation (R:/:A).
Proof.
  intros R A x [_ [y [z [H1 _]]]]. exists y. exists z. assumption.
Qed.

(* The restriction of R to A is a subclass of R.                                *)
Proposition InclR : forall (R A:Class), R:/:A :<=: R.
Proof.
  intros R A x [H1 _]. assumption.
Qed.

(* If the restriction of R to A holds at (x,y), then x is in A.                 *)
Proposition InAL : forall (R A:Class) (x y:U),
  (R:/:A) :(x,y): -> A x.
Proof.
  intros R A x y [_ H1]. apply Prod.Charac2 in H1. apply H1.
Qed.

(* If the restriction of R to A holds at (x,y), then y is in A.                 *)
Proposition InAR : forall (R A:Class) (x y:U),
  (R:/:A) :(x,y): -> A y.
Proof.
  intros R A x y [_ H1]. apply Prod.Charac2 in H1. apply H1.
Qed.



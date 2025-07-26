Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Functional.

(* A set is one-to-one iff both itself and its converse are functional.         *)
Definition OneToOne (f:U) : Prop := Functional f /\ Functional f^:-1:.


(* Uniqueness of left coordinate when one-to-one.                               *)
Proposition CharacL : forall (f:U), OneToOne f ->
  forall x y z, :(y,x): :< f -> :(z,x): :< f -> y = z.
Proof.
  intros f [_ H1] x y z H2 H3.
  apply H1 with x; apply Converse.Charac2Rev; assumption.
Qed.

(* Uniqueness of right coordinate when one-to-one.                              *)
Proposition CharacR : forall (f:U), OneToOne f ->
  forall x y z, :(x,y): :< f -> :(x,z): :< f -> y = z.
Proof.
  intros f [H1 _]. assumption.
Qed.

(* When two ordered pairs belong to a one-to-one set, equality between the      *)
(* first coordinates is equivalent to equality between the second coordinates.  *)
Proposition CoordEquiv : forall (f:U) (x1 x2 y1 y2:U),
  OneToOne f -> :(x1,y1): :< f -> :(x2,y2): :< f -> x1 = x2 <-> y1 = y2.
Proof.
  intros f x1 x2 y1 y2 H3 H1 H2. split; intros H4; subst.
  - apply CharacR with f x2; assumption.
  - apply CharacL with f y2; assumption.
Qed.

Proposition Converse : forall (f:U),
  OneToOne f -> OneToOne f^:-1:.
Proof.
  intros f [H1 H2]. split. 1: assumption. apply Functional.InclCompat with f.
  2: assumption. apply Converse.IsIncl.
Qed.




Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

(* The converse of a set.                                                       *)
Definition converse (a:U) : U := fromClass
  (Class.Converse.converse (toClass a))
  (ConverseIsSmall (toClass a) (SetIsSmall a)).

Proposition ConverseCharac : forall (a:U),
  forall x, x :< (converse a) <-> exists y z, x =:(z,y): /\ :(y,z): :< a.
Proof.
  intros a x. unfold converse. split; intros H1.
  - apply FromClassCharac, Class.Converse.ConverseCharac in H1. apply H1.
  - apply FromClassCharac, Class.Converse.ConverseCharac, H1.
Qed.

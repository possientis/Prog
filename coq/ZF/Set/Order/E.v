Require Import ZF.Class.Order.E.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Specify.

Module COE := ZF.Class.Order.E.

(* The binary relation on a induced by :<.                                      *)
Definition E (a:U) : U := {{ x :< a :x: a | COE.E }}.

Proposition Charac : forall (a x:U),
  x :< (E a) <-> exists y z, x = :(y,z): /\ y :< a /\ z :< a /\ y :< z.
Proof.
  intros a x. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [H1 H2].
    apply Prod.Charac in H1. destruct H1 as [y [z [H1 [H3 H4]]]].
    subst. apply COE.Charac2 in H2. exists y. exists z.
    split. 1: reflexivity. split. 1: assumption. split; assumption.
  - destruct H1 as [y [z [H1 [H2 [H3 H4]]]]]. subst.
    apply Specify.Charac. split.
    + apply Prod.Charac2. split; assumption.
    + apply COE.Charac2. assumption.
Qed.

Proposition Charac2 : forall (a y z:U),
  :(y,z): :< (E a) <-> y :< a /\ z :< a /\ y :< z.
Proof.
  intros a y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 [H2 [H3 H4]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H5]. subst.
    split. 1: assumption. split; assumption.
  - apply Charac. exists y. exists z. split. 1: reflexivity. assumption.
Qed.

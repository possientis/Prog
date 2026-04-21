Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.From2.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.RestrictOfClass.

Module CF2 := ZF.Class.Relation.Fun.From2.
Module SRR := ZF.Set.Relation.RestrictOfClass.

(* Given sets a and b and a Coq expression f representing a function with two   *)
(* argument sets, we define the associated function with domain axb.            *)
Definition from2 (a b:U) (f:U*U -> U) : U := (CF2.from2 f) :|: (a :x: b).

Proposition Charac : forall (f:U*U -> U) (a b x:U),
  x :< from2 a b f <-> exists u v, x = :(:(u,v):,f (u,v)): /\ u :< a /\ v :< b.
Proof.
  intros f a b x. split; intros H1.
  - apply SRR.Charac in H1. 2: apply CF2.IsFunctional.
    destruct H1 as [y [z [H1 [H2 H3]]]].
    apply Prod.Charac in H2. destruct H2 as [u [v [H2 [H4 H5]]]].
    apply CF2.Charac2 in H3. destruct H3 as [u' [v' [H3 H6]]].
    subst. apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H7]. subst.
    exists u', v'. split. 1: reflexivity. split; assumption.
  - destruct H1 as [u [v [H1 [H2 H3]]]].
    apply SRR.CharacRev with :(u,v): (f (u,v)); try assumption.
    + apply CF2.IsFunctional.
    + apply Prod.Charac. exists u, v. split. 1: reflexivity. split; assumption.
    + apply CF2.Satisfies.
Qed.

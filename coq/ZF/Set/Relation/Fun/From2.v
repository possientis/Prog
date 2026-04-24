Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.From2.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.

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

Proposition Charac2 : forall (f:U*U -> U) (a b u v w:U),
  :(:(u,v):,w): :< from2 a b f <-> u :< a /\ v :< b /\ w = f(u,v).
Proof.
  intros f a b u v w. split; intros H1.
  - apply Charac in H1. destruct H1 as [u' [v' [H1 [H2 H3]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H5]. subst.
    split. 1: assumption. split. 1: assumption. reflexivity.
  - destruct H1 as [H1 [H2 H3]]. subst. apply Charac.
    exists u. exists v. split. 1: reflexivity. split; assumption.
Qed.

Proposition Satisfies : forall (f:U*U -> U) (a b u v:U),
  u :< a -> v :< b -> :(:(u,v):, f(u,v)): :< from2 a b f.
Proof.
  intros f a b u v H1 H2. apply Charac2.
  split. 1: assumption. split. 1: assumption. reflexivity.
Qed.

Proposition IsFunctionOn : forall (f:U*U -> U) (a b:U),
  FunctionOn (from2 a b f) (a :x: b).
Proof.
  intros f a b. unfold from2.
  apply SRR.IsFunctionOn. 1: apply CF2.IsFunctional.
  intros p H1. apply Prod.Charac in H1.
  destruct H1 as [u [v [H1 [H2 H3]]]]. subst.
  apply CF2.DomainOf.
Qed.

Proposition Eval : forall (f:U*U -> U) (a b u v:U),
  u :< a -> v :< b -> (from2 a b f)!(:(u,v):) = f(u,v).
Proof.
  intros f a b u v H1 H2.
  apply (FunctionOn.Eval (from2 a b f) (a :x: b)).
  - apply IsFunctionOn.
  - apply Satisfies; assumption.
Qed.

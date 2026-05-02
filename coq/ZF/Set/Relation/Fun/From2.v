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
  (* An element of from2 a b f is precisely a pair ((u,v), f(u,v)) with u in a  *)
  (* and v in b, by definition of from2.                                        *)
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

(* Membership as a pair in from2 unpacks to witnesses and domain membership.    *)
Proposition Charac2 : forall (f:U*U -> U) (a b x y:U),
  :(x,y): :< from2 a b f <->
  exists u v, x = :(u,v): /\ y = f(u,v) /\ u :< a /\ v :< b.
Proof.
  (* Proof by Claude.                                                           *)
  (* Membership as a pair unpacks the witnesses via ordered-pair injectivity.   *)
  intros f a b x y. split; intros H1.
  - apply Charac in H1. destruct H1 as [u [v [H1 [H2 H3]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4]. subst.
    exists u, v. split. 1: reflexivity.
    split. 1: reflexivity. split; assumption.
  - destruct H1 as [u [v [H1 [H2 [H3 H4]]]]]. subst.
    apply Charac. exists u, v. split. 1: reflexivity. split; assumption.
Qed.

(* Fully explicit membership in from2 reduces to domain and value conditions.   *)
Proposition Charac3 : forall (f:U*U -> U) (a b u v w:U),
  :(:(u,v):,w): :< from2 a b f <-> u :< a /\ v :< b /\ w = f(u,v).
Proof.
  (* Proof by Claude.                                                           *)
  (* Follows from the pair-level characterization by ordered-pair injectivity.  *)
  intros f a b u v w. split; intros H1.
  - apply Charac2 in H1. destruct H1 as [u' [v' [H1 [H2 [H3 H4]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [Hu Hv]. subst u'. subst v'.
    split. 1: assumption. split. 1: assumption. assumption.
  - destruct H1 as [H1 [H2 H3]]. subst. apply Charac2.
    exists u, v. split. 1: reflexivity.
    split. 1: reflexivity. split; assumption.
Qed.

Proposition Satisfies : forall (f:U*U -> U) (a b u v:U),
  u :< a -> v :< b -> :(:(u,v):, f(u,v)): :< from2 a b f.
Proof.
  (* Proof by Claude.                                                           *)
  (* Follows directly from the membership characterization.                     *)
  intros f a b u v H1 H2. apply Charac3.
  split. 1: assumption. split. 1: assumption. reflexivity.
Qed.

Proposition IsFunctionOn : forall (f:U*U -> U) (a b:U),
  FunctionOn (from2 a b f) (a :x: b).
Proof.
  (* Proof by Claude.                                                           *)
  (* The relation from2 a b f is functional on a x b: for each (u,v) in a x b,  *)
  (* the pair ((u,v), f(u,v)) is the unique element with first component (u,v). *)
  intros f a b. unfold from2.
  apply SRR.IsFunctionOn. 1: apply CF2.IsFunctional.
  intros p H1. apply Prod.Charac in H1.
  destruct H1 as [u [v [H1 [H2 H3]]]]. subst.
  apply CF2.DomainOf.
Qed.

Proposition Eval : forall (f:U*U -> U) (a b u v:U),
  u :< a -> v :< b -> (from2 a b f)!(:(u,v):) = f(u,v).
Proof.
  (* Proof by Claude.                                                           *)
  (* Since ((u,v), f(u,v)) is in from2 a b f and the relation is functional,    *)
  (* the value of from2 a b f at (u,v) is f(u,v).                               *)
  intros f a b u v H1 H2.
  apply (FunctionOn.Eval (from2 a b f) (a :x: b)).
  - apply IsFunctionOn.
  - apply Satisfies; assumption.
Qed.

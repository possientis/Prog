Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.

Require Import ZF.Notation.Append.
Export ZF.Notation.Append.

Module SRF := ZF.Set.Relation.Fun.From.
Module SRI := ZF.Set.Relation.Inj.

(* The sum of two sets, formed by tagging the left and right components.        *)
Definition sum (a b:U) : U := :{ :0: }: :x: a :\/: :{ :1: }: :x: b.

(* Notation "a :++: b" := (sum a b)                                             *)
Global Instance SetAppend : Append U := { append := sum }.

(* The left injection from a to the disjoint sum of a and b.                    *)
Definition inL (a b:U) : U := SRF.from a (fun x => :(:0:,x):).

(* The right injection from b to the disjoint sum of a and b.                   *)
Definition inR (a b:U) : U := SRF.from b (fun y => :(:1:,y):).

(* The left injection is an injection from a to a ++ b.                         *)
Proposition IsInjL : forall (a b:U), Inj (inL a b) a (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. apply SRF.IsInj.
  - intros x H1. apply Union2.Charac. left.
    apply Prod.Charac2. split.
    + apply Single.IsIn.
    + assumption.
  - intros x y H1 H2 H3. apply OrdPair.Equal in H3. apply H3.
Qed.

(* The right injection is an injection from b to a ++ b.                        *)
Proposition IsInjR : forall (a b:U), Inj (inR a b) b (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. apply SRF.IsInj.
  - intros y H1. apply Union2.Charac. right.
    apply Prod.Charac2. split.
    + apply Single.IsIn.
    + assumption.
  - intros x y H1 H2 H3. apply OrdPair.Equal in H3. apply H3.
Qed.

(* The left injection is a function from a to a ++ b.                           *)
Proposition IsFunL : forall (a b:U), Fun (inL a b) a (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. apply SRI.IsFun, IsInjL.
Qed.

(* The right injection is a function from b to a ++ b.                          *)
Proposition IsFunR : forall (a b:U), Fun (inR a b) b (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b. apply SRI.IsFun, IsInjR.
Qed.

(* The left injection sends x to the left-tagged pair (0,x).                    *)
Proposition EvalL : forall (a b x:U),
  x :< a -> (inL a b)!x = :(:0:,x):.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b x H1. apply SRF.Eval. assumption.
Qed.

(* The right injection sends y to the right-tagged pair (1,y).                  *)
Proposition EvalR : forall (a b y:U),
  y :< b -> (inR a b)!y = :(:1:,y):.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b y H1. apply SRF.Eval. assumption.
Qed.

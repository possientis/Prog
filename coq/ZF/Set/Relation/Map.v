Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Specify.

(* The set of all maps from a to b.                                             *)
Definition map (a b:U) : U := {{ f :< :P(a :x: b) | fun f => Fun f a b }}.

(* The set of all surjections from a onto b.                                    *)
Definition onto (a b:U) : U := {{ f :< map a b | fun f => Onto f a b }}.

(* The set of all injections from a to b.                                       *)
Definition inj (a b:U) : U := {{ f :< map a b | fun f => Inj f a b }}.

(* The set of all bijections from a to b.                                       *)
Definition bij (a b:U) : U := {{ f :< map a b | fun f => Bij f a b }}.

(* A set belongs to map(a,b) iff it is a map from a to b.                       *)
Proposition CharacMap : forall (f a b:U),
  f :< map a b <-> Fun f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [_ H1]. assumption.
  - apply Specify.Charac. split. 2: assumption.
    apply Power.Charac. apply Prod.IsInclFun. assumption.
Qed.

(* A set belongs to onto(a,b) iff it is a surjection from a onto b.             *)
Proposition CharacOnto : forall (f a b:U),
  f :< onto a b <-> Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [_ H1]. assumption.
  - apply Specify.Charac. split. 2: assumption.
    apply CharacMap. apply Onto.IsFun. assumption.
Qed.

(* A set belongs to inj(a,b) iff it is an injection from a to b.                *)
Proposition CharacInj : forall (f a b:U),
  f :< inj a b <-> Inj f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [_ H1]. assumption.
  - apply Specify.Charac. split. 2: assumption.
    apply CharacMap. apply Inj.IsFun. assumption.
Qed.

(* A set belongs to bij(a,b) iff it is a bijection from a to b.                 *)
Proposition CharacBij : forall (f a b:U),
  f :< bij a b <-> Bij f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b. split; intros H1.
  - apply Specify.Charac in H1. destruct H1 as [_ H1]. assumption.
  - apply Specify.Charac. split. 2: assumption.
    apply CharacMap. apply Bij.IsFun. assumption.
Qed.

(* The set of maps from a to b is included in the power set of a x b.           *)
Proposition IsInclPower : forall (a b:U),
  map a b :<=: :P(a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1. apply Specify.Charac in H1. apply H1.
Qed.

(* The set of surjections from a onto b is included in the set of maps.         *)
Proposition IsInclOnto : forall (a b:U),
  onto a b :<=: map a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1. apply Specify.Charac in H1. apply H1.
Qed.

(* The set of injections from a to b is included in the set of maps.            *)
Proposition IsInclInj : forall (a b:U),
  inj a b :<=: map a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1. apply Specify.Charac in H1. apply H1.
Qed.

(* The set of bijections from a to b is included in the set of maps.            *)
Proposition IsInclBij : forall (a b:U),
  bij a b :<=: map a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1. apply Specify.Charac in H1. apply H1.
Qed.

(* The set of bijections from a to b is included in the set of surjections.     *)
Proposition IsInclBijOnto : forall (a b:U),
  bij a b :<=: onto a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1.
  apply CharacOnto. apply Bij.IsOnto. apply CharacBij. assumption.
Qed.

(* The set of bijections from a to b is included in the set of injections.      *)
Proposition IsInclBijInj : forall (a b:U),
  bij a b :<=: inj a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b f H1.
  apply CharacInj. apply Bij.IsInj. apply CharacBij. assumption.
Qed.

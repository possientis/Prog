Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Eval.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionalAt.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.Eval.
Export ZF.Notation.Eval.

(* Evaluate the class F at a, returning a set.                                  *)
Definition eval (F:Class) (a:U) : U :=
  fromClass (Class.Relation.Eval.eval F a) (Eval.IsSmall F a).

(* Notation "F ! a" := (eval F a)                                               *)
Global Instance ClassEval : Eval Class := { eval := eval }.

Proposition EquivCompat : forall (F G:Class) (a:U),
  F :~: G -> F!a = G!a.
Proof.
  intros F G a H1. apply FromClass.EquivCompat, Eval.EquivCompat. assumption.
Qed.

(* If F has a value at a, then y corresponds to a iff F!a = y.                  *)
Proposition HasValueAtEvalCharac : forall (F:Class) (a y:U),
  HasValueAt F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1. split; intros H2.
  - unfold eval. apply EqualToClass.
    apply Equiv.Tran with (Relation.Eval.eval F a).
    + apply ToFromClass.
    + apply Relation.Eval.WhenHasValueAt; assumption.
  - apply Relation.Eval.WhenHasValueAt. 1: assumption.
    unfold eval in H2. rewrite <- H2. apply Equiv.Sym, ToFromClass.
Qed.

(* If F has a value at a, then (a,F!a) satisfies the class F.                   *)
Proposition HasValueAtSatisfies : forall (F:Class) (a:U),
  HasValueAt F a -> F :(a,F!a):.
Proof.
  intros F a H1. apply HasValueAtEvalCharac.
  - assumption.
  - reflexivity.
Qed.

(* If F is functional at a and a lies in domain then F (a,y) iff F!a = y.       *)
Proposition FunctionalAtEvalCharac : forall (F:Class) (a y:U),
  FunctionalAt F a -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1 H2.
  apply HasValueAtEvalCharac, HasValueAtWhenFunctionalAt; assumption.
Qed.

(* If F is functional at a and a lies in domain then (a,F!a) satisfies F.       *)
Proposition FunctionalAtSatisfies : forall (F:Class) (a:U),
  FunctionalAt F a -> domain F a -> F :(a,F!a):.
Proof.
  intros F a H1 H2. apply FunctionalAtEvalCharac.
  - assumption.
  - assumption.
  - reflexivity.
Qed.

(* If F has no value at a then F!a is the empty set.                            *)
Proposition WhenNotHasValueAt : forall (F:Class) (a:U),
  ~ HasValueAt F a -> F!a = :0:.
Proof.
  intros F a H1. apply EqualToClass. unfold eval, zero, SetZero, empty.
  apply Equiv.Tran with (Relation.Eval.eval F a). 1: apply ToFromClass.
  apply Equiv.Tran with :0:.
  - apply Relation.Eval.WhenNotHasValueAt. assumption.
  - apply Equiv.Sym, ToFromClass.
Qed.

(* If F is not functional at a then F!a is the empty set.                       *)
Proposition WhenNotFunctionalAt : forall (F:Class) (a:U),
  ~ FunctionalAt F a -> F!a = :0:.
Proof.
  intros F a H1. apply WhenNotHasValueAt. intros H2. apply H1.
  apply HasValueAtAsInter. assumption.
Qed.

(* If a is not in domain of F then F!a is the empty set.                        *)
Proposition WhenNotInDomain : forall (F:Class) (a:U),
  ~ domain F a -> F!a = :0:.
Proof.
  intros F a H1. apply WhenNotHasValueAt. intros H2. apply H1.
  apply HasValueAtAsInter. assumption.
Qed.

(* If F is functional and a lies in domain of F then F (a,y) iff F!a = y.       *)
Proposition Charac : forall (F:Class) (a y:U),
  Functional F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1 H2.
  apply HasValueAtEvalCharac, HasValueAtWhenFunctional; assumption.
Qed.

(* If F is functional and a lies in domain of F then (a,F!a) satisfies F.       *)
Proposition Satisfies : forall (F:Class) (a:U),
  Functional F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a H1 H2. apply FunctionalAtSatisfies. 2: assumption.
  apply IsFunctionalAt. assumption.
Qed.

Proposition IsInRange : forall (F:Class) (a:U),
  Functional F -> domain F a -> range F (F!a).
Proof.
  intros F a H1 H2. exists a.
  apply Satisfies; assumption.

Qed.

(* Characterisation of the direct image F[A] in terms of evaluations of F.      *)
Proposition ImageCharac : forall (F A: Class), Functional F ->
  forall y, F:[A]: y <-> exists x, A x /\ domain F x /\ F!x = y.
Proof.
  intros F A H1 y. split; intros H2.
  - destruct H2 as [x [H2 H3]]. exists x. split. 1: assumption.
    assert (domain F x) as H4. { exists y. assumption. } split.
    + assumption.
    + apply Charac; assumption.
  - destruct H2 as [x [H2 [H3 H4]]]. exists x. split. 1: assumption.
    apply Charac; assumption.
Qed.


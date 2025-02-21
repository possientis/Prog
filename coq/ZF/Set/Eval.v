Declare Scope ZF_Set_Eval_scope.
Open    Scope ZF_Set_Eval_scope.

Require Import ZF.Axiom.Classic.
Require Import ZF.Class.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Eval.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionalAt.
Require Import ZF.Class.Image.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Range.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OrdPair.

(* Evaluate the class F at a, returning a set.                                  *)
Definition eval (F:Class) (a:U) : U := fromClass (Class.Eval.eval F a)
  (EvalIsSmall F a).

Notation "F ! a" := (eval F a)
  (at level 0, no associativity) : ZF_Set_Eval_scope.

(* If F has a value at a, then y corresponds to a iff F!a = y.                  *)
Proposition EvalWhenHasValueAt : forall (F:Class) (a y:U),
  HasValueAt F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1. split; intros H2.
  - unfold eval. apply ClassEquivSetEqual.
    apply ClassEquivTran with (Class.Eval.eval F a).
    + apply ToFromClass.
    + apply Class.Eval.EvalWhenHasValueAt; assumption.
  - apply Class.Eval.EvalWhenHasValueAt. 1: assumption.
    unfold eval in H2. rewrite <- H2. apply ClassEquivSym, ToFromClass.
Qed.

(* If F has a value at a, then (a,F!a) satisfies the class F.                   *)
Proposition EvalWhenHasValueAtSatisfies : forall (F:Class) (a:U),
  HasValueAt F a -> F :(a,F!a):.
Proof.
  intros F a H1. apply EvalWhenHasValueAt.
  - assumption.
  - reflexivity.
Qed.

(* If F is functional at a and a lies in domain then F (a,y) iff F!a = y.       *)
Proposition EvalWhenFunctionalAt : forall (F:Class) (a y:U),
  FunctionalAt F a -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1 H2.
  apply EvalWhenHasValueAt, HasValueAtWhenFunctionalAt; assumption.
Qed.

(* If F is functional at a and a lies in domain then (a,F!a) satisfies F.       *)
Proposition EvalWhenFunctionalAtSatisfies : forall (F:Class) (a:U),
  FunctionalAt F a -> domain F a -> F :(a,F!a):.
Proof.
  intros F a H1 H2. apply EvalWhenFunctionalAt.
  - assumption.
  - assumption.
  - reflexivity.
Qed.

(* If F has no value at a then F!a is the empty set.                            *)
Proposition EvalWhenNotHasValueAt : forall (F:Class) (a:U),
  ~ HasValueAt F a -> F!a = :0:.
Proof.
  intros F a H1. apply ClassEquivSetEqual. unfold eval, zero, SetZero, empty.
  apply ClassEquivTran with (Class.Eval.eval F a). 1: apply ToFromClass.
  apply ClassEquivTran with :0:.
  - apply Class.Eval.EvalWhenNotHasValueAt. assumption.
  - apply ClassEquivSym, ToFromClass.
Qed.

(* If F is not functional at a then F!a is the empty set.                       *)
Proposition EvalWhenNotFunctionalAt : forall (F:Class) (a:U),
  ~ FunctionalAt F a -> F!a = :0:.
Proof.
  intros F a H1. apply EvalWhenNotHasValueAt. intros H2. apply H1.
  apply HasValueAtAsInter. assumption.
Qed.

(* If a is not in domain of F then F!a is the empty set.                        *)
Proposition EvalWhenNotInDomain : forall (F:Class) (a:U),
  ~ domain F a -> F!a = :0:.
Proof.
  intros F a H1. apply EvalWhenNotHasValueAt. intros H2. apply H1.
  apply HasValueAtAsInter. assumption.
Qed.

(* If F is functional and a lies in domain of F then F (a,y) iff F!a = y.       *)
Proposition FunctionalEval : forall (F:Class) (a y:U),
  Functional F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1 H2.
  apply EvalWhenHasValueAt, HasValueAtWhenFunctional; assumption.
Qed.

(* If F is functional and a lies in domain of F then (a,F!a) satisfies F.       *)
Proposition FunctionalEvalSatisfies : forall (F:Class) (a:U),
  Functional F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a H1 H2. apply EvalWhenFunctionalAtSatisfies. 2: assumption.
  apply FunctionalIsFunctionalAt. assumption.
Qed.

Proposition FunctionalEvalIsInRange : forall (F:Class) (a:U),
  Functional F -> domain F a -> range F (F!a).
Proof.
  intros F a H1 H2. apply RangeCharac. exists a.
  apply FunctionalEvalSatisfies; assumption.

Qed.

(* Characterisation of the direct image F[A] in terms of evaluations of F.      *)
Proposition ImageEvalCharac : forall (F A: Class), Functional F ->
  forall y, F:[A]: y <-> exists x, A x /\ domain F x /\ F!x = y.
Proof.
  intros F A H1 y. split; intros H2.
  - apply (proj1 (ImageCharac _ _ _)) in H2. destruct H2 as [x [H2 H3]].
    exists x. split. 1: assumption.
    assert (domain F x) as H4. { apply DomainCharac. exists y. assumption. } split.
    + assumption.
    + apply FunctionalEval; assumption.
  - destruct H2 as [x [H2 [H3 H4]]].
    apply ImageCharac. exists x. split. 1: assumption.
    apply FunctionalEval; assumption.
Qed.


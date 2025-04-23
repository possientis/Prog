Declare Scope ZF_Class_Fun_scope.
Open    Scope ZF_Class_Fun_scope.

Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* F is a function from A to B.                                                 *)
Definition Fun (F A B:Class) : Prop := FunctionOn F A /\ range F :<=: B.

Notation "F :: A :-> B" := (Fun F A B)
  (at level 0, no associativity) : ZF_Class_Fun_scope.

Proposition ImageIsSmall : forall (F A B C:Class),
  F :: A :-> B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C [H1 _]. apply FunctionOn.ImageIsSmall with A. assumption.
Qed.

Proposition EvalCharac : forall (F A B:Class) (a y:U),
  F :: A :-> B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y [H1 _]. apply FunctionOn.EvalCharac. assumption.
Qed.

Proposition EvalSatisfies : forall (F A B:Class) (a:U),
  F :: A :-> B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a [H1 _]. apply FunctionOn.EvalSatisfies. assumption.
Qed.

Proposition EvalIsInRange : forall (F A B:Class) (a:U),
  (F :: A :-> B) -> A a -> B (F!a).
Proof.
  intros F A B a [H1 H2] H3. apply H2.
  apply FunctionOn.EvalIsInRange with A; assumption.
Qed.

Proposition ComposeIsFun : forall (F G A B C: Class),
  F :: A :-> B ->
  G :: B :-> C ->
  (G :.: F) :: A :-> C.
Proof.
  intros F G A B C [H1 H2] [H3 H4]. split.
  - apply ComposeIsFunctionOn with B; assumption.
  - apply InclTran with (range G). 2: assumption. apply ComposeRangeIsSmaller.
Qed.

Proposition DomainOfComposeCharac : forall (F G A B C:Class) (a:U),
  F :: A :-> B  ->
  G :: B :-> C  ->
  domain (G :.: F) a <-> A a.
Proof.
  intros F G A B C a [H1 H2] [H3 H4]. split; intros H5.
  - apply (FunctionOn.DomainOfComposeCharac F G A B a H1 H3) in H5.
    destruct H5 as [H5 H6]. assumption.
  - apply (FunctionOn.DomainOfComposeCharac F G A B a); try assumption.
    split. 1: assumption.  apply EvalIsInRange with A.
    + split; assumption.
    + assumption.
Qed.

Proposition ComposeEval : forall (F G A B C:Class) (a:U),
  F :: A :-> B  ->
  G :: B :-> C  ->
  A a           ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a [H1 H2] [H3 H4] H5.
  apply (FunctionOn.ComposeEval F G A B); try assumption.
  apply EvalIsInRange with A.
  - split; assumption.
  - assumption.
Qed.

Proposition ImageOfDomainIsRange : forall (F A B:Class),
  F :: A :-> B -> F:[A]: :~: range F.
Proof.
  intros F A B [H1 _]. apply FunctionOn.ImageOfDomainIsRange. assumption.
Qed.

Proposition InvImageOfRangeIsDomain : forall (F A B:Class),
  F :: A :-> B -> F^:-1::[range F]: :~: A.
Proof.
  intros F A B [H1 _]. apply FunctionOn.InvImageOfRangeIsDomain. assumption.
Qed.

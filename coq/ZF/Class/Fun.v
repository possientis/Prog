Declare Scope ZF_Class_Fun_scope.
Open    Scope ZF_Class_Fun_scope.

Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* F is a function from A to B.                                                 *)
Definition Fun (F A B:Class) : Prop := FunctionOn F A /\ range F :<=: B.

Notation "F :: A :-> B" := (Fun F A B)
  (at level 0, no associativity) : ZF_Class_Fun_scope.

Proposition FunImageIsSmall : forall (F A B C:Class),
  F :: A :-> B -> Small C -> Small F:[C]:.
Proof.
  intros F A B C [H1 _]. apply FunctionOnImageIsSmall with A. assumption.
Qed.

Proposition FunEval : forall (F A B:Class) (a y:U),
  F :: A :-> B -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A B a y [H1 _]. apply FunctionOnEval. assumption.
Qed.

Proposition FunEvalSatisfies : forall (F A B:Class) (a:U),
  F :: A :-> B -> A a -> F :(a,F!a):.
Proof.
  intros F A B a [H1 _]. apply FunctionOnEvalSatisfies. assumption.
Qed.

Proposition FunEvalIsInRange : forall (F A B:Class) (a:U),
  (F :: A :-> B) -> A a -> B (F!a).
Proof.
  intros F A B a [H1 H2] H3. apply H2.
  apply FunctionOnEvalIsInRange with A; assumption.
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

Proposition FunComposeDomainCharac : forall (F G A B C:Class) (a:U),
  F :: A :-> B  ->
  G :: B :-> C  ->
  domain (G :.: F) a <-> A a.
Proof.
  intros F G A B C a [H1 H2] [H3 H4]. split; intros H5.
  - apply (FunctionOnComposeDomainCharac F G A B a H1 H3) in H5.
    destruct H5 as [H5 H6]. assumption.
  - apply (FunctionOnComposeDomainCharac F G A B a); try assumption.
    split. 1: assumption.  apply FunEvalIsInRange with A.
    + split; assumption.
    + assumption.
Qed.

Proposition FunComposeEval : forall (F G A B C:Class) (a:U),
  F :: A :-> B  ->
  G :: B :-> C  ->
  A a           ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B C a [H1 H2] [H3 H4] H5.
  apply (FunctionOnComposeEval F G A B); try assumption.
  apply FunEvalIsInRange with A.
  - split; assumption.
  - assumption.
Qed.

Proposition FunRangeIsDomainImage : forall (F A B:Class),
  F :: A :-> B -> F:[A]: :~: range F.
Proof.
  intros F A B [H1 _]. apply FunctionOnRangeIsDomainImage. assumption.
Qed.

Proposition FunInvImageOfRangeIsDomain : forall (F A B:Class),
  F :: A :-> B -> F^:-1::[range F]: :~: A.
Proof.
  intros F A B [H1 _]. apply FunctionOnInvImageOfRangeIsDomain. assumption.
Qed.

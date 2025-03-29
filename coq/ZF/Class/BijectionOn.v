Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Function.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

(* F is a bijection defined on A.                                               *)
Definition BijectionOn (F A:Class) : Prop := Bijection F /\ domain F :~: A.

(* The image of a small class by a bijection class defined on any A is small.   *)
Proposition ImageIsSmall : forall (F A B:Class),
  BijectionOn F A -> Small B -> Small F:[B]:.
Proof.
  intros F A B [H1 _]. apply Bijection.ImageIsSmall. assumption.
Qed.

(* The inverse image of a small class by a bijection defined on any A is small. *)
Proposition InvImageIsSmall : forall (F A B:Class),
  BijectionOn F A -> Small B -> Small F^:-1::[B]:.
Proof.
  intros F A B [H1 _]. apply Bijection.InvImageIsSmall. assumption.
Qed.

(* A bijection is always a bijection defined on its domain. *)
Proposition BijectionIsBijectionOn : forall (F:Class),
  Bijection F -> BijectionOn F (domain F).
Proof.
  intros F H1. split. { assumption. } { apply Class.EquivRefl. }
Qed.

(* A bijection defined on A is a function defined on A.                         *)
Proposition IsFunctionOn : forall (F A:Class),
  BijectionOn F A -> FunctionOn F A.
Proof.
  intros F A [H1 H2]. apply Bijection.IsFunction in H1. split; assumption.
Qed.

(* A bijection defined on a small class is small.                               *)
Proposition IsSmall : forall (F A:Class),
  BijectionOn F A -> Small A -> Small F.
Proof.
  intros F A H1 H2. apply FunctionOn.IsSmall with A. 2: assumption.
  apply IsFunctionOn. assumption.
Qed.

Proposition ConverseIsBijectionOn : forall (F A B:Class),
  BijectionOn F A -> range F :~: B -> BijectionOn F^:-1: B.
Proof.
  intros F A B [H1 H2] H3. split.
  - apply Bijection.ConverseIsBijection. assumption.
  - apply Class.EquivTran with (range F). 2: assumption. apply ConverseDomain.
Qed.

Proposition ComposeIsBijectionOn : forall (F A G B:Class),
  BijectionOn F A ->
  BijectionOn G B ->
  range F :<=: B   ->
  BijectionOn (G :.: F) A.
Proof.
  intros F A G B [H1 H2] [H3 H4] H5. split.
  - apply Bijection.ComposeIsBijection; assumption.
  - apply Class.EquivTran with (domain F). 2: assumption.
    apply ComposeDomainIsSame. apply InclEquivCompatR with B. 2: assumption.
    apply Class.EquivSym. assumption.
Qed.

Proposition IsRestrict : forall (F A:Class),
  BijectionOn F A -> F :~: F:|:A.
Proof.
  intros F A H1. apply FunctionOnIsRestrict, IsFunctionOn. assumption.
Qed.

Proposition EvalCharac : forall (F A:Class) (a y:U),
  BijectionOn F A -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A a y H1. apply IsFunctionOn in H1.
  apply FunctionOn.EvalCharac. assumption.
Qed.

Proposition EvalSatisfies : forall (F A:Class) (a:U),
  BijectionOn F A -> A a -> F :(a,F!a):.
Proof.
  intros F A a H1. apply IsFunctionOn in H1.
  apply FunctionOn.EvalSatisfies. assumption.
Qed.

Proposition EvalIsInRange : forall (F A:Class) (a:U),
  BijectionOn F A -> A a -> range F (F!a).
Proof.
  intros F A a H1. apply IsFunctionOn in H1.
  apply FunctionOn.EvalIsInRange. assumption.
Qed.

Proposition ConverseEvalIsInDomain : forall (F A:Class) (b:U),
  BijectionOn F A -> range F b -> A (F^:-1:!b).
Proof.
  intros F A b [H1 H2] H3. apply H2.
  apply Bijection.ConverseEvalIsInDomain; assumption.
Qed.

Proposition ConverseEvalOfEval : forall (F A:Class) (x:U),
  BijectionOn F A -> A x -> F^:-1:!(F!x) = x.
Proof.
  intros F A x [H1 H2] H3. apply Bijection.ConverseEvalOfEval. 1: assumption.
  apply H2. assumption.
Qed.

Proposition EvalOfConverseEval : forall (F A:Class) (y:U),
  BijectionOn F A -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F A y [H1 H2]. apply Bijection.EvalOfConverseEval. assumption.
Qed.

Proposition DomainOfComposeCharac : forall (F G A B:Class) (a:U),
  BijectionOn F A ->
  BijectionOn G B ->
  domain (G :.: F) a <-> A a /\ B (F!a).
Proof.
  intros F G A B a H1 H2.
  apply IsFunctionOn in H1. apply IsFunctionOn in H2.
  apply FunctionOn.DomainOfComposeCharac; assumption.
Qed.

Proposition ComposeEval : forall (F G A B:Class) (a:U),
  BijectionOn F A ->
  BijectionOn G B ->
  A a             ->
  B (F!a)         ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G A B a H1 H2.
  apply IsFunctionOn in H1. apply IsFunctionOn in H2.
  apply FunctionOn.ComposeEval; assumption.
Qed.

Proposition ImageOfDomainIsRange : forall (F A:Class),
  BijectionOn F A -> F:[A]: :~: range F.
Proof.
  intros F A H1.
  apply FunctionOn.ImageOfDomainIsRange, IsFunctionOn. assumption.
Qed.

Proposition InvImageOfRangeIsDomain : forall (F A:Class),
  BijectionOn F A -> F^:-1::[range F]: :~: A.
Proof.
  intros F A H1.
  apply FunctionOn.InvImageOfRangeIsDomain, IsFunctionOn. assumption.
Qed.

Proposition InvImageOfImage : forall (F A B:Class),
  BijectionOn F A -> B :<=: A -> F^:-1::[ F:[B]: ]: :~: B.
Proof.
  intros F A B [H1 H2] H3. apply Bijection.InvImageOfImage. 1: assumption.
  apply InclEquivCompatR with A. 2: assumption. apply Class.EquivSym. assumption.
Qed.

Proposition ImageOfInvImage : forall (F A B:Class),
  BijectionOn F A -> B :<=: range F -> F:[ F^:-1::[B]: ]: :~: B.
Proof.
  intros F A B [H1 _]. apply Bijection.ImageOfInvImage. assumption.
Qed.

Proposition EvalInjective : forall (F A:Class) (x y:U),
  BijectionOn F A -> A x -> A y -> F!x = F!y -> x = y.
Proof.
  intros F A x y [H1 H2] H3 H4. apply Bijection.EvalInjective; try assumption;
  apply H2; assumption.
Qed.

Proposition EvalInImage : forall (F A B:Class) (a:U),
  BijectionOn F A -> A a -> F:[B]: (F!a) <-> B a.
Proof.
  intros F A B a [H1 H2] H3. apply Bijection.EvalInImage. 1: assumption.
  apply H2. assumption.
Qed.

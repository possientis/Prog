Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Image.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.


(* A class is a bijection if it is a relation and it is one-to-one.             *)
Definition Bijection (F:Class) : Prop := Relation F /\ OneToOne F.

Proposition BijectionImageIsSmall : forall (F A:Class),
  Bijection F -> Small A -> Small F:[A]:.
Proof.
  intros F A [_ H1]. apply OneToOneImageIsSmall. assumption.
Qed.

Proposition BijectionInvImageIsSmall : forall (F B:Class),
  Bijection F -> Small B -> Small F^:-1::[B]:.
Proof.
  intros F B [_ H1]. apply OneToOneInvImageIsSmall. assumption.
Qed.

Proposition BijectionIsFunction : forall (F:Class),
  Bijection F -> Function F.
Proof.
  intros F [H1 H2].
  apply OneToOneCharac in H2. destruct H2 as [H2 _].
  split; assumption.
Qed.

Proposition ConverseIsFunction : forall (F:Class),
  Bijection F -> Function F^:-1:.
Proof.
  intros F [H1 H2].
  apply OneToOneCharac in H2. destruct H2 as [_ H2].
  split. 2: assumption. apply ConverseIsRelation.
Qed.

Proposition ConverseIsBijection : forall (F:Class),
  Bijection F -> Bijection F^:-1:.
Proof.
  intros F [H1 H2]. split.
  - apply ConverseIsRelation.
  - apply ConverseIsOneToOne. assumption.
Qed.

(* The composition of two one-to-one classes is a bijection class.              *)
Proposition ComposeIsBijection2 : forall (F G:Class),
  OneToOne F -> OneToOne G -> Bijection (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRelation.
  - apply ComposeIsOneToOne; assumption.
Qed.

(* The composition of two bijection classes is a bijection class.               *)
Proposition ComposeIsBijection : forall (F G:Class),
  Bijection F -> Bijection G -> Bijection (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsBijection2; assumption.
Qed.

Proposition BijectionEval : forall (F:Class) (a y:U),
  Bijection F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y [_ H1]. apply OneToOneEval. assumption.
Qed.

Proposition BijectionEvalSatisfies : forall (F:Class) (a:U),
  Bijection F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a [_ H1]. apply OneToOneEvalSatisfies. assumption.
Qed.

Proposition BijectionEvalIsInRange : forall (F:Class) (a:U),
  Bijection F -> domain F a -> range F (F!a).
Proof.
  intros F a [_ H1]. apply OneToOneEvalIsInRange. assumption.
Qed.

Proposition BijectionEvalIsInDomain : forall (F:Class) (b:U),
  Bijection F -> range F b -> domain F (F^:-1:!b).
Proof.
  intros F y H1 H2. apply ConverseRange, BijectionEvalIsInRange.
  - apply ConverseIsBijection. assumption.
  - apply ConverseDomain. assumption.
Qed.

Proposition BijectionF_FEval : forall (F:Class) (x:U),
  Bijection F -> domain F x -> F^:-1:!(F!x) = x.
Proof.
  intros F x [_ H1]. apply OneToOneF_FEval. assumption.
Qed.

Proposition BijectionFF_Eval : forall (F:Class) (y:U),
  Bijection F -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F y [_ H1]. apply OneToOneFF_Eval. assumption.
Qed.

Proposition BijectionComposeDomainCharac : forall (F G:Class) (a:U),
  Bijection F -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a [_ H1]. apply OneToOneComposeDomainCharac. assumption.
Qed.

Proposition BijectionComposeEval : forall (F G:Class) (a:U),
  Bijection F     ->
  Bijection G     ->
  domain F a      ->
  domain G (F!a)  ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a [_ H1] [_ H2]. apply OneToOneComposeEval; assumption.
Qed.


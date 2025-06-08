Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

(* A class is a bijection if it is a relation and it is one-to-one.             *)
Definition Bijection (F:Class) : Prop := Relation F /\ OneToOne F.

(* A bijection class is a function class.                                       *)
Proposition IsFunction : forall (F:Class),
  Bijection F -> Function F.
Proof.
  intros F [H1 [H2 _]]. split; assumption.
Qed.

(* Two bijections are equal iff they have same domain and coincide pointwise.   *)
Proposition EquivCharac : forall (F G:Class),
  Bijection F ->
  Bijection G ->
  F :~: G   <->
  domain F :~: domain G  /\ forall x, domain F x -> F!x = G!x.
Proof.
  intros F G H1 H2. apply Function.EquivCharac; apply IsFunction; assumption.
Qed.

(* F need not be a bijection class.                                             *)
Proposition ImageOfDomain : forall (F:Class),
  F:[domain F]: :~: range F.
Proof.
  apply Range.ImageOfDomain.
Qed.

Proposition IsIncl : forall (F:Class),
  Bijection F -> F :<=: (domain F) :x: F:[domain F]:.
Proof.
  intros F H1. apply Function.IsIncl, IsFunction. assumption.
Qed.

Proposition ImageIsSmall : forall (F A:Class),
  Bijection F -> Small A -> Small F:[A]:.
Proof.
  intros F A [_ H1]. apply ImageIsSmall. assumption.
Qed.

(* A bijection class with a small domain is small.                              *)
Proposition IsSmall : forall (F:Class),
  Bijection F -> Small (domain F) -> Small F.
Proof.
  intros F H1. apply Function.IsSmall, IsFunction. assumption.
Qed.

Proposition InvImageIsSmall : forall (F B:Class),
  Bijection F -> Small B -> Small F^:-1::[B]:.
Proof.
  intros F B [_ H1]. apply InvImageIsSmall. assumption.
Qed.

Proposition ConverseIsFunction : forall (F:Class),
  Bijection F -> Function F^:-1:.
Proof.
  intros F [H1 [_ H2]]. split. 2: assumption. apply Converse.IsRelation.
Qed.

Proposition Converse : forall (F:Class),
  Bijection F -> Bijection F^:-1:.
Proof.
  intros F [H1 H2]. split.
  - apply Converse.IsRelation.
  - apply OneToOne.Converse. assumption.
Qed.

(* The composition of two one-to-one classes is a bijection class.              *)
Proposition OneToOneCompose : forall (F G:Class),
  OneToOne F -> OneToOne G -> Bijection (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply Compose.IsRelation.
  - apply ComposeIsOneToOne; assumption.
Qed.

(* The composition of two bijection classes is a bijection class.               *)
Proposition Compose: forall (F G:Class),
  Bijection F -> Bijection G -> Bijection (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply OneToOneCompose; assumption.
Qed.

Proposition EvalCharac : forall (F:Class) (a y:U),
  Bijection F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y [_ H1]. apply OneToOne.EvalCharac. assumption.
Qed.

Proposition Satisfies : forall (F:Class) (a:U),
  Bijection F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a [_ H1]. apply OneToOne.Satisfies. assumption.
Qed.

Proposition IsInRange : forall (F:Class) (a:U),
  Bijection F -> domain F a -> range F (F!a).
Proof.
  intros F a [_ H1]. apply OneToOne.IsInRange. assumption.
Qed.

Proposition ImageCharac : forall (F A: Class), Bijection F ->
  forall y, F:[A]: y <-> exists x, A x /\ domain F x /\ F!x = y.
Proof.
  intros F A [_ H1]. apply OneToOne.ImageCharac. assumption.
Qed.

Proposition ConverseEvalIsInDomain : forall (F:Class) (b:U),
  Bijection F -> range F b -> domain F (F^:-1:!b).
Proof.
  intros F y H1 H2. apply ConverseRange, IsInRange.
  - apply Converse. assumption.
  - apply ConverseDomain. assumption.
Qed.

Proposition ConverseEvalOfEval : forall (F:Class) (x:U),
  Bijection F -> domain F x -> F^:-1:!(F!x) = x.
Proof.
  intros F x [_ H1]. apply OneToOne.ConverseEvalOfEval. assumption.
Qed.

Proposition EvalOfConverseEval : forall (F:Class) (y:U),
  Bijection F -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F y [_ H1]. apply OneToOne.EvalOfConverseEval. assumption.
Qed.

Proposition DomainOfCompose : forall (F G:Class) (a:U),
  Bijection F -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a [_ H1]. apply OneToOne.DomainOfCompose. assumption.
Qed.

Proposition ComposeEval : forall (F G:Class) (a:U),
  Bijection F     ->
  Bijection G     ->
  domain F a      ->
  domain G (F!a)  ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a [_ H1] [_ H2]. apply OneToOne.ComposeEval; assumption.
Qed.

Proposition InvImageOfImage : forall (F A:Class),
  Bijection F -> A :<=: domain F -> F^:-1::[ F:[A]: ]: :~: A.
Proof.
  intros F A [_ H1]. apply OneToOne.InvImageOfImage. assumption.
Qed.

Proposition ImageOfInvImage : forall (F B:Class),
  Bijection F -> B :<=: range F -> F:[ F^:-1::[B]: ]: :~: B.
Proof.
  intros F B [_ H1]. apply OneToOne.ImageOfInvImage. assumption.
Qed.

Proposition EvalInjective : forall (F:Class) (x y:U),
  Bijection F -> domain F x -> domain F y -> F!x = F!y -> x = y.
Proof.
  intros F x y [_ H1]. apply OneToOne.EvalInjective. assumption.
Qed.

Proposition EvalInImage : forall (F A:Class) (a:U),
  Bijection F -> domain F a -> F:[A]: (F!a) <-> A a.
Proof.
  intros F A a [_ H1]. apply OneToOne.EvalInImage. assumption.
Qed.


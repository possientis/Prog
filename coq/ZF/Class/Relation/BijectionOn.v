Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Bijection.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.


(* F is a bijection defined on A.                                               *)
Definition BijectionOn (F A:Class) : Prop := Bijection F /\ domain F :~: A.

(* A bijection defined on A is a function defined on A.                         *)
Proposition IsFunctionOn : forall (F A:Class),
  BijectionOn F A -> FunctionOn F A.
Proof.
  intros F A [H1 H2]. apply Bijection.IsFunction in H1. split; assumption.
Qed.

(* Two bijections are equal iff they have same domain and coincide pointwise.   *)
Proposition EqualCharac : forall (F G A B:Class),
  BijectionOn F A ->
  BijectionOn G B ->
  F :~: G        <->
  A :~: B /\ forall x, A x -> F!x = G!x.
Proof.
  intros F G A B H1 H2. apply FunctionOn.EqualCharac;
  apply IsFunctionOn; assumption.
Qed.

Proposition ImageOfDomain : forall (F A:Class),
  BijectionOn F A -> F:[A]: :~: range F.
Proof.
  intros F A H1.
  apply FunctionOn.ImageOfDomain, IsFunctionOn. assumption.
Qed.

Proposition IsIncl : forall (F A:Class),
  BijectionOn F A -> F :<=: A :x: F:[A]:.
Proof.
  intros F A H1. apply FunctionOn.IsIncl, IsFunctionOn. assumption.
Qed.

(* The image of a small class by a bijection class defined on any A is small.   *)
Proposition ImageIsSmall : forall (F A B:Class),
  BijectionOn F A -> Small B -> Small F:[B]:.
Proof.
  intros F A B [H1 _]. apply Bijection.ImageIsSmall. assumption.
Qed.

(* A bijection defined on a small class is small.                               *)
Proposition IsSmall : forall (F A:Class),
  BijectionOn F A -> Small A -> Small F.
Proof.
  intros F A H1 H2. apply FunctionOn.IsSmall with A. 2: assumption.
  apply IsFunctionOn. assumption.
Qed.

Proposition InvImageOfRange : forall (F A:Class),
  BijectionOn F A -> F^:-1::[range F]: :~: A.
Proof.
  intros F A H1.
  apply FunctionOn.InvImageOfRange, IsFunctionOn. assumption.
Qed.

Proposition RangeIsSmall : forall (F A:Class),
  BijectionOn F A -> Small A -> Small (range F).
Proof.
  intros F A H1 H2. apply Small.EquivCompat with F:[A]:.
  - apply ImageOfDomain. assumption.
  - apply ImageIsSmall with A; assumption.
Qed.

Proposition Compose : forall (F A G B:Class),
  BijectionOn F A ->
  BijectionOn G B ->
  range F :<=: B   ->
  BijectionOn (G :.: F) A.
Proof.
  intros F A G B [H1 H2] [H3 H4] H5. split.
  - apply Bijection.Compose; assumption.
  - apply Equiv.Tran with (domain F). 2: assumption.
    apply Compose.DomainIsSame. apply Incl.EquivCompatR with B. 2: assumption.
    apply Equiv.Sym. assumption.
Qed.

Proposition EvalCharac : forall (F A:Class) (a y:U),
  BijectionOn F A -> A a -> F :(a,y): <-> F!a = y.
Proof.
  intros F A a y H1. apply IsFunctionOn in H1.
  apply FunctionOn.EvalCharac. assumption.
Qed.

Proposition Satisfies : forall (F A:Class) (a:U),
  BijectionOn F A -> A a -> F :(a,F!a):.
Proof.
  intros F A a H1. apply IsFunctionOn in H1.
  apply FunctionOn.Satisfies. assumption.
Qed.

Proposition IsInRange : forall (F A:Class) (a:U),
  BijectionOn F A -> A a -> range F (F!a).
Proof.
  intros F A a H1. apply IsFunctionOn in H1.
  apply FunctionOn.IsInRange. assumption.
Qed.

Proposition ImageCharac : forall (F A B: Class), BijectionOn F A ->
  forall y, F:[B]: y <-> exists x, B x /\ A x /\ F!x = y.
Proof.
  intros F A B H1. apply FunctionOn.ImageCharac, IsFunctionOn. assumption.
Qed.

Proposition ImageSetCharac : forall (F A:Class) (a:U), BijectionOn F A ->
  forall y, y :< F:[a]: <-> exists x, x :< a /\ A x /\ F!x = y.
Proof.
  intros F A a H1. apply FunctionOn.ImageSetCharac, IsFunctionOn. assumption.
Qed.

Proposition DomainOfCompose : forall (F G A B:Class) (a:U),
  BijectionOn F A ->
  BijectionOn G B ->
  domain (G :.: F) a <-> A a /\ B (F!a).
Proof.
  intros F G A B a H1 H2.
  apply IsFunctionOn in H1. apply IsFunctionOn in H2.
  apply FunctionOn.DomainOfCompose; assumption.
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

Proposition RangeCharac : forall (F A:Class) (y:U),
  BijectionOn F A -> range F y <-> exists x, A x /\ F!x = y.
Proof.
  intros F A y H1. apply FunctionOn.RangeCharac, IsFunctionOn. assumption.
Qed.

Proposition RangeIsNotEmpty : forall (F A:Class),
  BijectionOn F A -> A :<>: :0: -> range F :<>: :0:.
Proof.
  intros F A H1. apply FunctionOn.RangeIsNotEmpty, IsFunctionOn. assumption.
Qed.

Proposition IsRestrict : forall (F A:Class),
  BijectionOn F A -> F :~: F:|:A.
Proof.
  intros F A H1. apply FunctionOn.IsRestrict, IsFunctionOn. assumption.
Qed.

(* The inverse image of a small class by a bijection defined on any A is small. *)
Proposition InvImageIsSmall : forall (F A B:Class),
  BijectionOn F A -> Small B -> Small F^:-1::[B]:.
Proof.
  intros F A B [H1 _]. apply Bijection.InvImageIsSmall. assumption.
Qed.

Proposition Converse : forall (F A B:Class),
  BijectionOn F A -> range F :~: B -> BijectionOn F^:-1: B.
Proof.
  intros F A B [H1 H2] H3. split.
  - apply Bijection.Converse. assumption.
  - apply Equiv.Tran with (range F). 2: assumption. apply Converse.Domain.
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

Proposition InvImageOfImage : forall (F A B:Class),
  BijectionOn F A -> B :<=: A -> F^:-1::[ F:[B]: ]: :~: B.
Proof.
  intros F A B [H1 H2] H3. apply Bijection.InvImageOfImage. 1: assumption.
  apply Incl.EquivCompatR with A. 2: assumption. apply Equiv.Sym. assumption.
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

(* A bijection is always a bijection defined on its domain. *)
Proposition BijectionIsBijectionOn : forall (F:Class),
  Bijection F -> BijectionOn F (domain F).
Proof.
  intros F H1. split. { assumption. } { apply Equiv.Refl. }
Qed.

Proposition Inter2Image : forall (F A B C:Class),
  BijectionOn F A -> F:[B :/\: C]: :~: F:[B]: :/\: F:[C]:.
Proof.
  intros F A B C H1. apply Bijection.Inter2Image, H1.
Qed.

Proposition DiffImage : forall (F A B C:Class),
  BijectionOn F A -> F:[B :\: C]: :~: F:[B]: :\: F:[C]:.
Proof.
  intros F A B C H1. apply Bijection.DiffImage, H1.
Qed.

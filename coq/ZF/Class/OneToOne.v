Require Import ZF.Binary.
Require Import ZF.Binary.Converse.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.OneToOne.
Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.InvImage.
Require Import ZF.Class.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

Definition OneToOne (F:Class) : Prop := Binary.OneToOne.OneToOne (toBinary F).

(* A class is one-to-one iff it and its converse are functional.                *)
Proposition OneToOneCharac : forall (F:Class),
  OneToOne F <-> Functional F /\ Functional F^:-1:.
Proof.
  unfold OneToOne, Binary.OneToOne.OneToOne. split; intros [H1 H2].
  - split. 1: assumption. unfold converse, Functional.
    apply Binary.Functional.FunctionalEquivCompat
      with (Binary.Converse.converse (toBinary F)). 2: assumption.
    apply BinaryEquivSym, ToFromBinary.
  - split. 1: assumption. unfold converse, Functional in H2.
    apply Binary.Functional.FunctionalEquivCompat
      with (toBinary (fromBinary (Binary.Converse.converse (toBinary F)))).
    2: assumption. apply ToFromBinary.
Qed.

Proposition OneToOneIsFunctional : forall (F:Class),
  OneToOne F -> Functional F.
Proof.
  intros F H1. apply OneToOneCharac in H1. destruct H1 as [H1 _]. assumption.
Qed.

Proposition OneToOneConverseIsFunctional : forall (F:Class),
  OneToOne F -> Functional F^:-1:.
Proof.
  intros F H1. apply OneToOneCharac in H1. destruct H1 as [_ H1]. assumption.
Qed.

Proposition OneToOneInvImageOfImageIsLess : forall (F A:Class),
  OneToOne F -> F^:-1::[ F:[A]: ]: :<=: A.
Proof.
  intros F A H1. apply FunctionalInvImageOfImageIsLess.
  apply OneToOneConverseIsFunctional. assumption.
Qed.

(* Same as the 'Functional' counterpart. Duplicated here for convenience.       *)
Proposition OneToOneInvImageOfImageIsMore : forall (F A:Class),
  A :<=: domain F -> A :<=: F^:-1::[ F:[A]: ]:.
Proof.
  intros F A H1 x H2. specialize (H1 x H2).
  apply (proj1 (DomainCharac _ _)) in H1. destruct H1 as [y H1].
  apply InvImageCharac. exists y. split. 2: assumption.
  apply ImageCharac. exists x. split; assumption.
Qed.

Proposition OneToOneImageOfInvImageIsLess : forall (F B:Class),
  OneToOne F -> F:[ F^:-1::[B]: ]: :<=: B.
Proof.
  intros F B H1. apply FunctionalImageOfInvImageIsLess.
  apply OneToOneIsFunctional. assumption.
Qed.

(* Same as the 'Functional' counterpart. Duplicated here for convenience.       *)
Proposition OneToOneImageOfInvImageIsMore : forall (F B:Class),
  B :<=: range F -> B :<=: F:[ F^:-1::[B]: ]:.
Proof.
  intros F B H1 y H2. specialize (H1 y H2).
  apply (proj1 (RangeCharac _ _)) in H1. destruct H1 as [x H1].
  apply ImageCharac. exists x. split. 2: assumption.
  apply InvImageCharac. exists y. split; assumption.
Qed.

(* Uniqueness of left coordinate when one-to-one.                               *)
Proposition OneToOneCharacL : forall (F:Class), OneToOne F ->
  forall x y z, F :(y,x): -> F :(z,x): -> y = z.
Proof.
  intros F H1. apply OneToOneCharac in H1. destruct H1 as [_ H1].
  intros x y z H2 H3. apply H1 with x.
  - apply ConverseCharac2. assumption.
  - apply ConverseCharac2. assumption.
Qed.

(* Uniqueness of right coordinate when one-to-one.                              *)
Proposition OneToOneCharacR : forall (F:Class), OneToOne F ->
  forall x y z, F :(x,y): -> F :(x,z): -> y = z.
Proof.
  intros F H1. apply OneToOneCharac in H1. destruct H1 as [H1 _]. assumption.
Qed.

Proposition OneToOneImageIsSmall : forall (F A:Class),
  OneToOne F -> Small A -> Small F:[A]:.
Proof.
  intros F A H1. apply OneToOneCharac in H1. destruct H1 as [H1 _].
  apply FunctionalImageIsSmall. assumption.
Qed.

Proposition OneToOneInvImageIsSmall : forall (F B:Class),
  OneToOne F -> Small B -> Small F^:-1::[B]:.
Proof.
  intros F B H1. apply OneToOneCharac in H1. destruct H1 as [_ H1].
  apply FunctionalImageIsSmall. assumption.
Qed.

(* When two ordered pairs belong to a one-to-one class, equality between the    *)
(* first coordinates is equivalent to equality between the second coordinates.  *)
Proposition OneToOneCoordEquiv : forall (F:Class) (x1 x2 y1 y2:U),
  OneToOne F -> F :(x1,y1): -> F :(x2,y2): -> x1 = x2 <-> y1 = y2.
Proof.
  intros F x1 x2 y1 y2 H3 H1 H2. split; intros H4.
  - subst. apply OneToOneCharacR with F x2; assumption.
  - subst. apply OneToOneCharacL with F y2; assumption.
Qed.

Proposition ConverseIsOneToOne : forall (F:Class),
  OneToOne F -> OneToOne F^:-1:.
Proof.
  intros F H1. apply OneToOneCharac in H1. destruct H1 as [H1 H2].
  apply OneToOneCharac. split. 1: assumption.
  apply FunctionalInclCompat with F. 2: assumption.
  apply ConverseOfConverseIncl.
Qed.

Proposition OneToOneEvalCharac : forall (F:Class) (a y:U),
  OneToOne F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y H1. apply OneToOneCharac in H1. destruct H1 as [H1 _].
  apply FunctionalEvalCharac. assumption.
Qed.

Proposition OneToOneEvalSatisfies : forall (F:Class) (a:U),
  OneToOne F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a H1. apply OneToOneCharac in H1. destruct H1 as [H1 _].
  apply FunctionalEvalSatisfies. assumption.
Qed.

Proposition OneToOneEvalIsInRange : forall (F:Class) (a:U),
  OneToOne F -> domain F a -> range F (F!a).
Proof.
  intros F a H1. apply OneToOneCharac in H1. destruct H1 as [H1 _].
  apply FunctionalEvalIsInRange. assumption.
Qed.

Proposition OneToOneEvalIsInDomain : forall (F:Class) (b:U),
  OneToOne F -> range F b -> domain F (F^:-1:!b).
Proof.
  intros F b H1 H2. apply ConverseRange, OneToOneEvalIsInRange.
  - apply ConverseIsOneToOne. assumption.
  - apply ConverseDomain. assumption.
Qed.

(* The composition of two one-to-one classes is one-to-one.                     *)
Proposition ComposeIsOneToOne : forall (F G:Class),
  OneToOne F -> OneToOne G -> OneToOne (G :.: F).
Proof.
  intros F G H1 H2.
  apply OneToOneCharac in H1. destruct H1 as [H1 H3].
  apply OneToOneCharac in H2. destruct H2 as [H2 H4].
  apply OneToOneCharac. split.
  - apply ComposeIsFunctional; assumption.
  - apply FunctionalEquivCompat with (converse F :.: converse G).
    + apply ClassEquivSym, ComposeConverse.
    + apply ComposeIsFunctional; assumption.
Qed.

Proposition OneToOneF_FEval : forall (F:Class) (x:U),
  OneToOne F -> domain F x -> F^:-1:!(F!x) = x.
Proof.
  intros F x H1 H3. apply OneToOneCharac in H1. destruct H1 as [H1 H2].
  apply FunctionalEvalCharac.
  - assumption.
  - apply ConverseDomain, RangeCharac. exists x.
    apply FunctionalEvalSatisfies; assumption.
  - apply ConverseCharac2. apply FunctionalEvalSatisfies; assumption.
Qed.

Proposition OneToOneFF_Eval : forall (F:Class) (y:U),
  OneToOne F -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F y H1 H3. apply OneToOneCharac in H1. destruct H1 as [H1 H2].
  assert (H4 := H3). apply (proj1 (RangeCharac _ _)) in H4.  destruct H4 as [x H4].
  assert (F^:-1:!y = x) as H5. { apply FunctionalEvalCharac.
    - assumption.
    - apply ConverseDomain. assumption.
    - apply ConverseCharac2. assumption. }
  rewrite H5. apply FunctionalEvalCharac.
  - assumption.
  - apply DomainCharac. exists y. assumption.
  - assumption.
Qed.

Proposition OneToOneComposeDomainCharac : forall (F G:Class) (a:U),
  OneToOne F -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a H1. apply OneToOneCharac in H1. destruct H1 as [H1 _].
  apply FunctionalComposeDomainCharac. assumption.
Qed.

Proposition OneToOneComposeEval : forall (F G:Class) (a:U),
  OneToOne F      ->
  OneToOne G      ->
  domain F a      ->
  domain G (F!a)  ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a H1 H2. apply OneToOneCharac in H1. apply OneToOneCharac in H2.
  destruct H1 as [H1 _]. destruct H2 as [H2 _].
  apply FunctionalComposeEval; assumption.
Qed.


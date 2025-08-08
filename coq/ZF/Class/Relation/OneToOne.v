Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

(* A class is one-to-one iff both itself and its converse are functional.       *)
Definition OneToOne (F:Class) : Prop := Functional F /\ Functional F^:-1:.

(* Uniqueness of left coordinate when one-to-one.                               *)
Proposition CharacL : forall (F:Class), OneToOne F ->
  forall x y z, F :(y,x): -> F :(z,x): -> y = z.
Proof.
  intros F [_ H1] x y z H2 H3.
  apply H1 with x; apply Converse.Charac2Rev; assumption.
Qed.

(* Uniqueness of right coordinate when one-to-one.                              *)
Proposition CharacR : forall (F:Class), OneToOne F ->
  forall x y z, F :(x,y): -> F :(x,z): -> y = z.
Proof.
  intros F [H1 _]. assumption.
Qed.

Proposition ImageIsSmall : forall (F A:Class),
  OneToOne F -> Small A -> Small F:[A]:.
Proof.
  intros F A [H1 _]. apply Image.IsSmall. assumption.
Qed.

Proposition InvImageIsSmall : forall (F B:Class),
  OneToOne F -> Small B -> Small F^:-1::[B]:.
Proof.
  intros F B [_ H1]. apply Image.IsSmall. assumption.
Qed.

(* When two ordered pairs belong to a one-to-one class, equality between the    *)
(* first coordinates is equivalent to equality between the second coordinates.  *)
Proposition CoordEquiv : forall (F:Class) (x1 x2 y1 y2:U),
  OneToOne F -> F :(x1,y1): -> F :(x2,y2): -> x1 = x2 <-> y1 = y2.
Proof.
  intros F x1 x2 y1 y2 H3 H1 H2. split; intros H4; subst.
  - apply CharacR with F x2; assumption.
  - apply CharacL with F y2; assumption.
Qed.

Proposition Converse : forall (F:Class),
  OneToOne F -> OneToOne F^:-1:.
Proof.
  intros F [H1 H2]. split. 1: assumption. apply Functional.InclCompat with F.
  2: assumption. apply Converse.IsIncl.
Qed.

Proposition EvalCharac : forall (F:Class) (a y:U),
  OneToOne F -> domain F a -> F :(a,y): <-> F!a = y.
Proof.
  intros F a y [H1 _]. apply EvalOfClass.Charac. assumption.
Qed.

Proposition Satisfies : forall (F:Class) (a:U),
  OneToOne F -> domain F a -> F :(a,F!a):.
Proof.
  intros F a [H1 _]. apply EvalOfClass.Satisfies. assumption.
Qed.

Proposition IsInRange : forall (F:Class) (a:U),
  OneToOne F -> domain F a -> range F (F!a).
Proof.
  intros F a [H1 _]. apply EvalOfClass.IsInRange. assumption.
Qed.

Proposition ImageCharac : forall (F A:Class), OneToOne F ->
  forall y, F:[A]: y <-> exists x, A x /\ domain F x /\ F!x = y.
Proof.
  intros F A [H1 _]. apply EvalOfClass.ImageCharac. assumption.
Qed.

Proposition ConverseEvalIsInDomain : forall (F:Class) (b:U),
  OneToOne F -> range F b -> domain F (F^:-1:!b).
Proof.
  intros F b H1 H2. apply Converse.Range, IsInRange.
  - apply Converse. assumption.
  - apply Converse.Domain. assumption.
Qed.

(* The composition of two one-to-one classes is one-to-one.                     *)
Proposition Compose : forall (F G:Class),
  OneToOne F -> OneToOne G -> OneToOne (G :.: F).
Proof.
  intros F G [H1 H2] [H3 H4]. split.
  - apply Compose.IsFunctional; assumption.
  - apply Functional.EquivCompat with (converse F :.: converse G).
    + apply Equiv.Sym, Compose.Converse.
    + apply Compose.IsFunctional; assumption.
Qed.

Proposition ConverseEvalOfEval : forall (F:Class) (x:U),
  OneToOne F -> domain F x -> F^:-1:!(F!x) = x.
Proof.
  intros F x [H1 H2] H3. apply EvalOfClass.Charac. 1: assumption.
  - apply Converse.Domain. exists x. apply EvalOfClass.Satisfies; assumption.
  - apply Converse.Charac2Rev, EvalOfClass.Satisfies; assumption.
Qed.

Proposition EvalOfConverseEval : forall (F:Class) (y:U),
  OneToOne F -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F y [H1 H2] H3. assert (H4 := H3). destruct H4 as [x H4].
  assert (F^:-1:!y = x) as H5. {
    apply EvalOfClass.Charac. 1: assumption.
    - apply Converse.Domain. assumption.
    - apply Converse.Charac2Rev. assumption. }
  rewrite H5. apply EvalOfClass.Charac; try assumption. exists y. assumption.
Qed.

Proposition DomainOfCompose : forall (F G:Class) (a:U),
  OneToOne F -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a [H1 _]. apply Compose.FunctionalDomainCharac. assumption.
Qed.

Proposition ComposeEval : forall (F G:Class) (a:U),
  OneToOne F      ->
  OneToOne G      ->
  domain F a      ->
  domain G (F!a)  ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a [H1 _] [H2 _]. apply Compose.Eval; assumption.
Qed.

Proposition InvImageOfImage : forall (F A:Class),
  OneToOne F -> A :<=: domain F -> F^:-1::[ F:[A]: ]: :~: A.
Proof.
  intros F A [H1 H2] H3. apply DoubleInclusion. split.
  - apply InvImage.OfImageIsLess. assumption.
  - apply InvImage.OfImageIsMore. assumption.
Qed.

Proposition ImageOfInvImage : forall (F B:Class),
  OneToOne F -> B :<=: range F -> F:[ F^:-1::[B]: ]: :~: B.
Proof.
  intros F B [H1 H2] H3. apply DoubleInclusion. split.
  - apply InvImage.ImageIsLess. assumption.
  - apply InvImage.ImageIsMore. assumption.
Qed.

Proposition EvalInjective : forall (F:Class) (x y:U),
  OneToOne F -> domain F x -> domain F y -> F!x = F!y -> x = y.
Proof.
  intros F x y H1 H2 H3 H4.
  assert (F :(x,F!x):) as H5. { apply Satisfies; assumption. }
  assert (F :(y,F!y):) as H6. { apply Satisfies; assumption. }
  rewrite <- H4 in H6. revert H5 H6. apply CharacL. assumption.
Qed.

Proposition EvalInImage : forall (F A:Class) (a:U),
  OneToOne F -> domain F a -> F:[A]: (F!a) <-> A a.
Proof.
  intros F A a H1 H2. split; intros H3.
  - destruct H3 as [x [H3 H4]].
    assert (x = a) as H5. {
      apply CharacL with F (F!a); try assumption.
      apply Satisfies; assumption. }
    subst. assumption.
  - exists a. split. 1: assumption. apply Satisfies; assumption.
Qed.

Proposition Restrict : forall (F A:Class),
  OneToOne F  -> OneToOne (F:|:A).
Proof.
  intros F A [H1 H2]. split.
  - apply Restrict.IsFunctional. assumption.
  - intros z y x H3 H4.
    apply Converse.Charac2 in H3. apply Restrict.Charac2 in H3.
    apply Converse.Charac2 in H4. apply Restrict.Charac2 in H4.
    destruct H3 as [H3 H5]. destruct H4 as [H4 H6].
    apply H2 with z; apply Converse.Charac2Rev; assumption.
Qed.

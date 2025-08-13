Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Relation.Snd.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.Pipe.
Export ZF.Notation.Pipe.

(* Restricting a class F to a class A.                                          *)
Definition restrict (F A:Class) : Class := fun x =>
  exists y z, x = :(y,z): /\ A y /\ F :(y,z):.

(* Notation "F :|: A" := (restrict F A)                                         *)
Global Instance ClassPipe : Pipe Class Class := { pipe := restrict }.

Proposition Charac2 : forall (F A:Class) (y z:U),
  (F:|:A) :(y,z): <-> A y /\ F :(y,z):.
Proof.
  intros F A y z. split; intros H1.
  - destruct H1 as [y' [z' [H1 H2]]]. apply WhenEqual in H1.
    destruct H1 as [H1 H1']. subst. assumption.
  - exists y. exists z. split.
    + reflexivity.
    + assumption.
Qed.

Proposition EquivCompat : forall (F G A B:Class),
  F :~: G -> A :~: B -> F:|:A :~: G:|:B.
Proof.
  intros F G A B H1 H2 x. split; intros H3;
  destruct H3 as [y [z [H3 [H4 H5]]]]; subst; apply Charac2; split.
  - apply H2. assumption.
  - apply H1. assumption.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.

Proposition EquivCompatL : forall (F G A:Class),
  F :~: G -> F:|:A :~: G:|:A.
Proof.
  intros F G A H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

Proposition EquivCompatR : forall (F A B:Class),
  A :~: B -> F:|:A :~: F:|:B.
Proof.
  intros F A B H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

(* The restriction is always a relation.                                        *)
Proposition IsRelation : forall (F A:Class), Relation (F:|:A).
Proof.
  intros F A x H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

(* The restriction of a functional class is functional.                         *)
Proposition IsFunctional : forall (F A:Class),
  Functional F -> Functional (F:|:A).
Proof.
  intros F A H1 x y z H2 H3.
  apply Charac2 in H2. destruct H2 as [_ H2].
  apply Charac2 in H3. destruct H3 as [_ H3].
  apply H1 with x; assumption.
Qed.

(* The domain of the restriction F|A is the intersection of A and domain F.     *)
Proposition DomainOf : forall (F A:Class),
  domain (F:|:A) :~: A :/\: domain F.
Proof.
  intros F A x. split; intros H1.
  - destruct H1 as [y H1]. apply Charac2 in H1.
    destruct H1 as [H1 H2]. split. 1: assumption. exists y. apply H2.
  - destruct H1 as [H1 H2]. destruct H2 as [y H2]. exists y.
    apply Charac2. split; assumption.
Qed.

(* The range of the restriction F|A is the direct image by F of A.              *)
Proposition RangeOf : forall (F A:Class),
  range (F:|:A) :~: F:[A]:.
Proof.
  intros F A y. split; intros H1.
  - destruct H1 as [x H1]. apply Charac2 in H1.
    destruct H1 as [H1 H2]. exists x. split; assumption.
  - destruct H1 as [x [H1 H2]]. exists x. apply Charac2. split; assumption.
Qed.

(* The range of the restriction is a subclass of the range.                     *)
Proposition RangeIsIncl : forall (F A:Class),
  range (F:|:A) :<=: range F.
Proof.
  intros F A. apply Incl.EquivCompatL with F:[A]:.
  - apply Equiv.Sym, RangeOf.
  - apply Range.ImageIsIncl.
Qed.

(* The restriction of a functional class to a small class is small.             *)
Proposition IsSmall : forall (F A:Class),
  Functional F -> Small A -> Small (F:|:A).
Proof.
  intros F A H1 H2. apply Relation.IsSmall.
  - apply IsRelation.
  - apply IsFunctional. assumption.
  - apply Small.EquivCompat with (A :/\: domain F).
    + apply Equiv.Sym, DomainOf.
    + apply Inter2.IsSmallL. assumption.
Qed.

(* A restriction is a subclass of the original class.                           *)
Proposition IsIncl : forall (F A:Class),
  F:|:A :<=: F.
Proof.
  intros F A x [y [z [H1 [_ H2]]]]. subst. assumption.
Qed.

Proposition IsSmall' : forall (F A:Class),
  Small F -> Small (F:|:A).
Proof.
  intros F A H1. apply Bounded.WhenSmaller with F.
  2: assumption. apply IsIncl.
Qed.

(* The image of any class by a small class is small.                            *)
Proposition ImageIsSmall : forall (F A:Class),
  Small F -> Small F:[A]:.
Proof.
  intros F A H1. apply Small.EquivCompat with Snd:[F:|:A]:.
  - apply Equiv.Tran with (range (F:|:A)).
    + apply Range.ImageBySnd.
    + apply RangeOf.
  - apply Image.IsSmall.
    + apply Snd.IsFunctional.
    + apply Bounded.WhenSmaller with F. 2: assumption. apply IsIncl.
Qed.

(* A class is a relation iff it equals the restriction to its domain.           *)
Proposition RelationCharac : forall (F:Class),
  Relation F <-> F :~: F :|: domain F.
Proof.
  intros F. split; intros H1.
  - intros x. split; intros H2.
    + destruct (H1 x H2) as [y [z H3]]. exists y. exists z. split.
      * assumption.
      * split.
        { exists z. subst. assumption. }
        { subst. assumption. }
    + destruct H2 as [y [z [H3 [_ H4]]]]. rewrite H3. apply H4.
  - intros x H2. apply H1 in H2. destruct H2 as [y [z [H2 _]]].
    exists y. exists z. assumption.
Qed.

Proposition TowerProperty : forall (F A B:Class),
  A :<=: B -> (F:|:B) :|: A :~: F:|:A.
Proof.
  intros F A B H1 x. split; intros H2.
  - destruct H2 as [y [z [H2 [H3 H4]]]]. apply Charac2 in H4.
    destruct H4 as [H4 H5]. exists y. exists z. split. 1: assumption.
    split; assumption.
  - destruct H2 as [y [z [H2 [H3 H4]]]]. exists y. exists z. split.
    1: assumption. split. 1: assumption. apply Charac2. split.
    2: assumption. apply H1. assumption.
Qed.

Proposition LesserThanRangeIsSmall : forall (F A B:Class),
  Functional F -> Small B -> A :<=: range (F:|:B) -> Small A.
Proof.
  intros F A B H1 H2 H3.
  apply Bounded.WhenSmaller with (range (F:|:B)). 1: assumption.
  apply Small.EquivCompat with F:[B]:. 1: apply Equiv.Sym, RangeOf.
  apply Image.IsSmall; assumption.
Qed.

Proposition Eval : forall (F A:Class) (x:U), Functional F -> A x ->
  (F:|:A)!x = F!x.
Proof.
  intros F A x H1 H2.
  assert (Functional (F:|:A)) as H3. { apply IsFunctional. assumption. }
  assert (domain F x \/ ~ domain F x) as H4. { apply LawExcludedMiddle. }
  remember (F!x) as y eqn:E. destruct H4 as [H4|H4].
  - assert (domain (F:|:A) x) as H5. { apply DomainOf. split; assumption. }
    apply EvalOfClass.Charac; try assumption.
    apply Charac2. split. 1: assumption. rewrite E.
    apply EvalOfClass.Satisfies; assumption.
  - assert (~ domain (F:|:A) x) as H5. {
      intros H5. destruct H5 as [z H5]. apply Charac2 in H5.
      destruct H5 as [H5 H6]. apply H4.  exists z. assumption. }
    assert (y = :0:) as H6. {
      rewrite E. apply EvalOfClass.WhenNotInDomain. assumption. }
    rewrite H6. apply EvalOfClass.WhenNotInDomain. assumption.
Qed.

Proposition LesserThanRangeOfRestrict : forall (F A:Class),
  Functional F ->
  (exists a, A :\: range (F:|:toClass a) :~: :0:) ->
  Small A.
Proof.
  intros F A H1 [a H2]. apply Diff.WhenEmpty in H2.
  apply LesserThanRangeIsSmall with F (toClass a).
  - assumption.
  - apply SetIsSmall.
  - assumption.
Qed.


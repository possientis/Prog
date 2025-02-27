Require Import ZF.Axiom.Classic.
Require Import ZF.Binary.Restrict.
Require Import ZF.Class.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Domain.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Core.Pipe.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.
Export ZF.Core.Pipe.

(* Restricting a class F to a class A.                                          *)
Definition restrict (F A:Class) : Class
  := fromBinary (Binary.Restrict.restrict (toBinary F) A).

(* Notation "F :|: A" := (restrict F A)                                         *)
Global Instance ClassPipe : Pipe Class Class := { pipe := restrict }.

Proposition RestrictCharac : forall (F A:Class) (x:U),
  (F:|:A) x <-> exists y, exists z, x = :(y,z): /\ A y /\ F :(y,z):.
Proof.
  intros F A x. split; intros H1.
  - apply H1.
  - destruct H1 as [y [z [H2 [H3 H4]]]].
    unfold pipe, ClassPipe, restrict, fromBinary.
    unfold Binary.Restrict.restrict, toBinary.
    exists y. exists z. split.
    + assumption.
    + split; assumption.
Qed.

Proposition RestrictCharac2 : forall (F A:Class) (y z:U),
  (F:|:A) :(y,z): <-> A y /\ F :(y,z):.
Proof.
  intros F A y z. split; intros H1.
  - apply RestrictCharac in H1.
    destruct H1 as [y' [z' [H1 H2]]]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H1']. subst. apply H2.
  - exists y. exists z. split.
    + reflexivity.
    + apply H1.
Qed.

Proposition RestrictEquivCompat : forall (F G A B:Class),
  F :~: G -> A :~: B -> F:|:A :~: G:|:B.
Proof.
  intros F G A B H1 H2 x. split; intros H3;
  apply (proj1 (RestrictCharac _ _ _)) in H3; destruct H3 as [y [z [H3 [H4 H5]]]];
  subst; apply RestrictCharac2; split.
  - apply H2. assumption.
  - apply H1. assumption.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.

Proposition RestrictEquivCompatL : forall (F G A:Class),
  F :~: G -> F:|:A :~: G:|:A.
Proof.
  intros F G A H1. apply RestrictEquivCompat.
  - assumption.
  - apply ClassEquivRefl.
Qed.

Proposition RestrictEquivCompatR : forall (F A B:Class),
  A :~: B -> F:|:A :~: F:|:B.
Proof.
  intros F A B H1. apply RestrictEquivCompat.
  - apply ClassEquivRefl.
  - assumption.
Qed.

(* The restriction is always a relation.                                        *)
Proposition RestrictIsRelation : forall (F A:Class), Relation (F:|:A).
Proof.
  intros F A. apply FromBinaryIsRelation.
Qed.

(* The restriction of a functional class is always functional.                  *)
Proposition RestrictIsFunctional : forall (F A:Class),
  Functional F -> Functional (F:|:A).
Proof.
  intros F A H1 x y z H2 H3. apply H1 with x.
  - apply RestrictCharac2 in H2. destruct H2 as [_ H2]. assumption.
  - apply RestrictCharac2 in H3. destruct H3 as [_ H3]. assumption.
Qed.

(* The domain of the restriction F|A is the intersection A/\domain F.           *)
Proposition DomainOfRestrict : forall (F A:Class),
  domain (F:|:A) :~: A :/\: domain F.
Proof.
  intros F A x. split; intros H1.
  - destruct H1 as [y H1]. apply RestrictCharac2 in H1.
    destruct H1 as [H1 H2]. split. 1: assumption. exists y. apply H2.
  - destruct H1 as [H1 H2]. destruct H2 as [y H2]. exists y.
    apply RestrictCharac2. split; assumption.
Qed.

(* The restriction of a functional class to a small class is small.             *)
Proposition RestrictIsSmall : forall (F A:Class),
  Functional F -> Small A -> Small (F:|:A).
Proof.

  (* Let F and A be arbitrary classes. *)
  intros F A.

  (* We assume that F is functional. *)
  intros H1. assert (Functional F) as A'. { apply H1. } clear A'.

  (* We assume that A is small. *)
  intros H2. assert (Small A) as A'. { apply H2. } clear A'.

  (* And we need to show that the restriction F|A is small. *)
  assert (Small (F:|:A)) as A'. 2: apply A'.

  (* Using the fact that a function defined on a small class is small. *)
  apply FunctionOnIsSmall with (domain (F:|:A)).

  (* We first need to show that F|A is a function defined on its domain. *)
  - assert (FunctionOn (F:|:A) (domain (F:|:A))) as A'. 2: apply A'.

  (* Any function is always a function defined on its domain. *)
    apply FunctionIsFunctionOn.

  (* So we only need to show that F|A is a function. *)
    assert (Function (F:|:A)) as A'. 2: apply A'. split.

  (* Which follows from the fact that F|A is always a relation. *)
    + apply RestrictIsRelation.

  (* And the fact that F|A is functional since F is. *)
    + apply RestrictIsFunctional, H1.

  (* It remains to prove that the domain of F|A is small. *)
  - assert (Small (domain (F:|:A))) as A'. 2: apply A'.

  (* However, the domain of F|A is A /\ domain F. *)
    apply SmallEquivCompat with (A:/\:domain F).
      1: { apply ClassEquivSym, DomainOfRestrict. }

  (* So we need to show that A/\domain F is small. *)
    assert (Small (A:/\:domain F)) as A'. 2: apply A'.

  (* which follows from the assumption that A is small. *)
  apply InterIsSmallL, H2.

Qed.

(* The range of the restriction F|A is the direct image F[A].                   *)
Proposition ImageIsRangeOfRestrict : forall (F A:Class),
  F:[A]: :~: range (F:|:A).
Proof.
  intros F A y. split; intros H1.
  - unfold image in H1. destruct H1 as [x [H1 H2]].
    exists x. unfold toBinary. apply RestrictCharac2. split; assumption.
  - destruct H1 as [x H1]. apply RestrictCharac2 in H1.
    destruct H1 as [H1 H2]. exists x. unfold toBinary. split; assumption.
Qed.

(* A restriction is always a subclass of the original class.                    *)
Proposition RestrictIsSubClass : forall (F A:Class),
  F:|:A :<=: F.
Proof.
  intros F A x H1. apply RestrictCharac in H1. destruct H1 as [y [z [H1 [_ H2]]]].
  rewrite H1. apply H2.
Qed.

(* A class is a relation iff it equals the restriction to its domain.           *)
Proposition RelationIsRestrict : forall (F:Class),
  Relation F <-> F :~: F :|: domain F.
Proof.
  intros F. split; intros H1.
  - intros x. split; intros H2.
    + destruct (H1 x H2) as [y [z H3]]. apply RestrictCharac.
      exists y. exists z. split.
      * assumption.
      * split.
        { exists z. subst. assumption. }
        { subst. assumption. }
    + apply RestrictCharac in H2. destruct H2 as [y [z [H3 [_ H4]]]].
      rewrite H3. apply H4.
  - intros x H2. apply H1 in H2.
    apply (proj1 (RestrictCharac _ _ _)) in H2. destruct H2 as [y [z [H2 _]]].
    exists y. exists z. assumption.
Qed.

Proposition FunctionOnIsRestrict : forall (F A:Class),
  FunctionOn F A -> F :~: F:|:A.
Proof.
  intros F A [[H1 H2] H3]. apply ClassEquivTran with (F:|:domain F).
  - apply RelationIsRestrict. assumption.
  - apply RestrictEquivCompatR. assumption.
Qed.

Proposition RestrictTowerProperty : forall (F A B:Class),
  A :<=: B -> (F:|:B) :|: A :~: F:|:A.
Proof.
  intros F A B H1 x. split; intros H2.
  - apply (proj1 (RestrictCharac _ _ _)) in H2. destruct H2 as [y [z [H2 [H3 H4]]]].
    apply RestrictCharac2 in H4. destruct H4 as [H4 H5]. apply RestrictCharac.
    exists y. exists z. split.
    + assumption.
    + split; assumption.
  - apply (proj1 (RestrictCharac _ _ _)) in H2. destruct H2 as [y [z [H2 [H3 H4]]]].
    apply RestrictCharac. exists y. exists z. split.
    + assumption.
    + split.
      * assumption.
      * apply RestrictCharac2. split.
        { apply H1. assumption. }
        { assumption. }
Qed.

Proposition LesserThanRangeOfRestrictIsSmall : forall (F A B:Class),
  Functional F -> Small B -> A :<=: range (F:|:B) -> Small A.
Proof.
  intros F A B H1 H2 H3.
  apply LesserThanSmallIsSmall with (range (F:|:B)). 1: assumption.
  apply SmallEquivCompat with F:[B]:. 1: apply ImageIsRangeOfRestrict.
  apply FunctionalImageIsSmall; assumption.
Qed.

Proposition RestrictEval : forall (F A:Class) (x:U), Functional F -> A x ->
  (F:|:A)!x = F!x.
Proof.
  intros F A x H1 H2.
  assert (Functional (F:|:A)) as H3. { apply RestrictIsFunctional. assumption. }
  assert (domain F x \/ ~ domain F x) as H4. { apply LawExcludedMiddle. }
  remember (F!x) as y eqn:E. destruct H4 as [H4|H4].
  - assert (domain (F:|:A) x) as H5. {
      apply DomainOfRestrict, InterCharac. split; assumption. }
    apply FunctionalEvalCharac.
    + assumption.
    + assumption.
    + apply RestrictCharac2. split. 1: assumption. rewrite E.
      apply FunctionalEvalSatisfies; assumption.
  - assert (~ domain (F:|:A) x) as H5. { intros H5.
      destruct H5 as [z H5].
      apply RestrictCharac2 in H5. destruct H5 as [H5 H6]. apply H4.
      exists z. assumption. }
    assert (y = :0:) as H6. { rewrite E. apply EvalWhenNotInDomain. assumption. }
    rewrite H6. apply EvalWhenNotInDomain. assumption.
Qed.

Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Truncate.

Export ZF.Notation.Pipe.

Module CRD := ZF.Class.Relation.Domain.
Module CFL := ZF.Class.Relation.Functional.
Module CRR := ZF.Class.Relation.Range.

Module SRD := ZF.Set.Relation.Domain.
Module SFL := ZF.Set.Relation.Functional.
Module SRR := ZF.Set.Relation.Range.

Definition restrict (F:Class) (a:U) : U := truncate (F:|:toClass a).

(* Notation "F :|: a" := (restrict F a)                                         *)
Global Instance SetOfClassPipe : Pipe Class U U := { pipe := restrict }.

Proposition ToClass : forall (F:Class) (a:U), CFL.Functional F ->
  toClass (F:|:a) :~: F:|:toClass a.
Proof.
  intros F a H1. apply Truncate.WhenSmall. apply Restrict.IsSmall.
  1: assumption. apply Small.SetIsSmall.
Qed.

Proposition ToClassWhenSmall : forall (F:Class) (a:U),
  Small F -> toClass (F:|:a) :~: F:|:toClass a.
Proof.
  intros F a H1. apply Truncate.WhenSmall, Restrict.IsSmall'. assumption.
Qed.

Proposition EquivCompat : forall (F G:Class) (a:U),
  F :~: G -> F:|:a = G:|:a.
Proof.
  intros F G a H1. apply Truncate.EquivCompat, Restrict.EquivCompatL. assumption.
Qed.

Proposition Charac : forall (F:Class) (a x:U), CFL.Functional F ->
  x :< F:|:a -> exists y z, x = :(y,z): /\ y :< a /\ F :(y,z):.
Proof.
  intros F a x H1 H2. apply ToClass in H2. 2: assumption.
  destruct H2 as [y [z H2]]. exists y. exists z. assumption.
Qed.

Proposition CharacRev : forall (F:Class) (a x y z:U), CFL.Functional F ->
  x = :(y,z): -> y :< a -> F :(y,z): -> x :< F:|:a.
Proof.
  intros F a x y z H1 H2 H3 H4. apply ToClass. 1: assumption.
  exists y. exists z. split. 1: assumption. split; assumption.
Qed.

Proposition Charac2 : forall (F:Class) (a y z:U), CFL.Functional F ->
  :(y,z): :< (F:|:a) -> y :< a /\ F :(y,z):.
Proof.
  intros F a y z H1 H2. apply Charac in H2. destruct H2 as [y' [z' [H2 [H3 H4]]]].
  apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H5]. subst. 2: assumption.
  split; assumption.
Qed.

Proposition Charac2Rev : forall (F:Class) (a y z:U), CFL.Functional F ->
  y :< a -> F :(y,z): -> :(y,z): :< (F:|:a).
Proof.
  intros F a y z H1 H2 H3. apply CharacRev with y z; try assumption. reflexivity.
Qed.

(* The restriction of a class by a set is always a relation.                    *)
Proposition IsRelation : forall (F:Class) (a:U), CFL.Functional F ->
  Relation (F:|:a).
Proof.
  intros F a H1 x H2. apply Charac in H2. 2: assumption.
  destruct H2 as [y [z [H2 _]]]. exists y. exists z. assumption.
Qed.

(* The restriction of a functional class is a functional set.                   *)
Proposition IsFunctional : forall (F:Class) (a:U), 
  CFL.Functional F -> SFL.Functional (F:|:a).
Proof.
  intros F a H1 x y z H2 H3.
  apply Charac2 in H2. 2: assumption. destruct H2 as [_ H2].
  apply Charac2 in H3. 2: assumption. destruct H3 as [_ H3].
  apply H1 with x; assumption.
Qed.

Proposition IsFunction : forall (F:Class) (a:U), CFL.Functional F ->
  Function (F:|:a).
Proof.
  intros F a H1. split.
  - apply IsRelation. assumption.
  - apply IsFunctional. assumption.
Qed.

(* The domain of the restriction F|a is the intersection of a and domain F.     *)
Proposition DomainOf : forall (F:Class) (a:U), CFL.Functional F ->
  SRD.domain (F:|:a) = :{ a | CRD.domain F }:.
Proof.
  intros F a H1. apply DoubleInclusion. split; intros x H2.
  - apply SRD.Charac in H2. destruct H2 as [y H2]. apply Charac2 in H2.
    2: assumption. destruct H2 as [H2 H3]. apply Specify.Charac.
    split. 1: assumption. exists y. assumption.
  - apply Specify.Charac in H2. destruct H2 as [H2 [y H3]].
    apply SRD.Charac. exists y. apply Charac2Rev; assumption.
Qed.

Proposition DomainWhenIncl : forall (F:Class) (a:U), CFL.Functional F ->
  toClass a :<=: CRD.domain F -> SRD.domain (F:|:a) = a.
Proof.
  intros F a H1 H2. rewrite DomainOf. 2: assumption.
  apply DoubleInclusion. split; intros x H3.
  - apply Specify.Charac in H3. apply H3.
  - apply Specify.Charac. split. 1: assumption. apply H2. assumption.
Qed.

(* The range of the restriction f|a is the direct image by f of a.              *)
Proposition RangeOf : forall (F:Class) (a:U), CFL.Functional F ->
  SRR.range (F:|:a) = F:[a]:.
Proof.
  intros F a H1. apply DoubleInclusion. split; intros y H2.
  - apply SRR.Charac in H2. destruct H2 as [x H2].
    apply Charac2 in H2. 2: assumption. destruct H2 as [H2 H3].
    apply ImageByClass.CharacRev with x; assumption.
  - apply ImageByClass.Charac in H2. 2: assumption. destruct H2 as [x [H2 H3]].
    apply SRR.Charac. exists x. apply Charac2Rev; assumption.
Qed.

(* The range of the restriction is a subset of the range.                       *)
Proposition RangeIsIncl : forall (F:Class) (a y:U), CFL.Functional F ->
  y :< SRR.range (F:|:a) -> CRR.range F y.
Proof.
  intros F a y H1 H2. apply SRR.Charac in H2. destruct H2 as [x H2].
  apply Charac2 in H2. 2: assumption. destruct H2 as [H2 H3].
  exists x. assumption.
Qed.

(* A restriction is a subset of the original class.                             *)
Proposition IsIncl : forall (F:Class) (a x:U), CFL.Functional F ->
  x :< F:|:a -> F x.
Proof.
  intros F a x H1 H2. apply Charac in H2. 2: assumption.
  destruct H2 as [y [z [H2 [H3 H4]]]]. subst. assumption.
Qed.

Proposition TowerProperty : forall (F:Class) (a b:U), CFL.Functional F ->
  a :<=: b -> (F:|:b) :|: a = F:|:a.
Proof.
  intros F a b H1 H2. apply DoubleInclusion. split; intros x H3.
  - apply Restrict.Charac in H3. destruct H3 as [y [z [H3 [H4 H5]]]].
    apply Charac in H5. 2: assumption. destruct H5 as [y' [z' [H5 [H6 H7]]]].
    symmetry in H5. apply OrdPair.WhenEqual in H5. destruct H5 as [H5 H8]. subst.
    apply Charac2Rev; assumption.
  - apply Charac in H3. 2: assumption. destruct H3 as [y [z [H3 [H4 H5]]]].
    apply Restrict.Charac. exists y. exists z. split. 1: assumption.
    split. 1: assumption. apply Charac2Rev; try assumption. apply H2. assumption.
Qed.

Proposition Eval : forall (F:Class) (a x:U), CFL.Functional F -> x :< a ->
  (F:|:a)!x = F!x.
Proof.
  intros F a x H1 H2.
  assert (SFL.Functional (F:|:a)) as H3. { apply IsFunctional. assumption. }
  assert (CRD.domain F x \/ ~ CRD.domain F x) as H4. { apply LawExcludedMiddle. }
  remember (F!x) as y eqn:E. destruct H4 as [H4|H4].
  - assert (x :< SRD.domain (F:|:a)) as H5. {
      rewrite DomainOf. 2: assumption. apply Specify.Charac. split; assumption. }
    apply Eval.Charac; try assumption. apply Charac2Rev; try assumption.
    rewrite E. apply EvalOfClass.Satisfies; assumption.
  - assert (~ x :< SRD.domain (F:|:a)) as H5. {
      intros H5. apply SRD.Charac in H5. destruct H5 as [z H5].
      apply Charac2 in H5. 2: assumption. destruct H5 as [H5 H6]. apply H4.
      exists z. assumption. }
    assert (y = :0:) as H6. {
      rewrite E. apply EvalOfClass.WhenNotInDomain. assumption. }
    rewrite H6. apply Eval.WhenNotInDomain. assumption.
Qed.

Proposition WhenEmpty : forall (F:Class) (a:U),
  a = :0: -> F :|: a = :0:.
Proof.
  intros F a H1. apply Truncate.WhenEmpty. intros x. split; intros H2.
  - destruct H2 as [y [z [_ [H2 _]]]]. rewrite H1 in H2.
    apply Empty.Charac in H2. contradiction.
  - contradiction.
Qed.


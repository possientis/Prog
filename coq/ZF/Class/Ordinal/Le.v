Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.

Module CEM := ZF.Class.Empty.
Module COC := ZF.Class.Ordinal.Core.
Module SEM := ZF.Set.Empty.
Module SOC := ZF.Set.Ordinal.Core.

(* Lexicographical order on On x On.                                            *)
Definition Le : Class := fun x =>
  exists a b c d, x = :( :(a,b): , :(c,d): ): /\ (a :< c \/ (a = c /\ b :< d)).

Proposition Charac2 : forall (x y:U),
  Le :(x,y): <->
  exists a b c d, x = :(a,b): /\ y = :(c,d): /\ (a :< c \/ (a = c /\ b :< d)).
Proof.
  intros x y. split; intros H1.
  - destruct H1 as [a [b [c [d [H1 H2]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3].
    exists a. exists b. exists c. exists d. split. 1: assumption.
    split; assumption.
  - destruct H1 as [a [b [c [d [H1 [H2 H3]]]]]].
    exists a. exists b. exists c. exists d. subst.
    split. 2: assumption. reflexivity.
Qed.

Proposition Charac4 : forall (a b c d:U),
  Le :( :(a,b): , :(c,d): ): <-> a :< c \/ (a = c /\ b :< d).
Proof.
  intros a b c d. split; intros H1.
  - apply Charac2 in H1. destruct H1 as [a' [b' [c' [d' [H1 [H2 H3]]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4].
    apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H5].
    subst. assumption.
  - apply Charac2. exists a. exists b. exists c. exists d.
    split. 1: reflexivity. split. 1: reflexivity. assumption.
Qed.

(* A non-empty subclass of On x On has an Le-minimal element.                   *)
Proposition HasMinimal : forall (A:Class),
  A :<=: On :x: On          ->
  A :<>: :0:                ->

  exists a b,
    On a                    /\
    On b                    /\
    Minimal Le A :(a,b):.
Proof.
  intros A H1 H2.
  assert (domain A :<>: :0:) as H3. {
    apply CEM.HasElem in H2. destruct H2 as [x H2].
      assert ((On :x: On) x) as H3. { apply H1. assumption. }
      destruct H3 as [y [z [H3 _]]]. subst. apply CEM.HasElem.
      exists y. exists z. assumption. }
  assert (domain A :<=: On) as H4. {
    intros x [y H4]. apply H1 in H4. apply Prod.Charac2 in H4. apply H4. }
  assert (exists a,
    On a /\ domain A a /\ forall y, domain A y -> a :<=: y) as H5. {
    apply SOC.HasMinimal; assumption. }
  destruct H5 as [a [H5 [H6 H7]]].
  remember (fun b => A :(a,b):) as B eqn:H8.
  assert (B :<=: On) as H9. {
    intros b H9. rewrite H8 in H9. apply H1 in H9. apply Prod.Charac2 in H9.
    apply H9. }
  assert (B :<>: :0:) as H10. {
    destruct H6 as [b H6]. apply CEM.HasElem. exists b. rewrite H8. assumption. }
  assert (exists b, On b /\ B b /\ forall z, B z -> b :<=: z) as H11. {
    apply SOC.HasMinimal; assumption. }
  destruct H11 as [b [H11 [H12 H13]]].
  assert (Minimal Le A :(a,b):) as H14. {
    split.
    - rewrite H8 in H12. assumption.
    - intros x H14 H15. assert (H16 := H14). apply H1 in H14.
      destruct H14 as [y [z [H14 [H17 H18]]]]. subst.
      apply Charac4 in H15. destruct H15 as [H15|[H15 H19]].
      + apply NoElemLoop1 with y. apply H7. 2: assumption. exists z. assumption.
      + subst. apply NoElemLoop1 with z. apply H13; assumption. }
  exists a. exists b. split. 1: assumption. split; assumption.
Qed.

(* Le is founded on On x On.                                                    *)
Proposition IsFounded : Founded Le (On :x: On).
Proof.
  intros x H1 H2.
  assert (exists a b, On a /\ On b /\ Minimal Le (toClass x) :(a,b):) as H3. {
    apply HasMinimal. 1: assumption. apply SEM.NotEmptyToClass. assumption. }
  destruct H3 as [a [b [H3 [H4 H5]]]].
  exists :(a,b):. assumption.
Qed.

(* Le is total om On x On.                                                      *)
Proposition IsTotal : Total Le (On :x: On).
Proof.
  intros x y H1 H2.
  destruct H1 as [a [b [H1 [H3 H4]]]]. destruct H2 as [c [d [H2 [H5 H6]]]]. subst.
  assert (a = c \/ a :< c \/ c :< a) as H7. { apply SOC.IsTotal; assumption. }
  assert (b = d \/ b :< d \/ d :< b) as H8. { apply SOC.IsTotal; assumption. }
  destruct H7 as [H7|[H7|H7]].
  - destruct H8 as [H8|[H8|H8]].
    + subst. left. reflexivity.
    + subst. right. left.
      apply Charac4. right. split. 1: reflexivity. assumption.
    + subst. right. right.
      apply Charac4. right. split. 1: reflexivity. assumption.
  - right. left. apply Charac4. left. assumption.
  - right. right. apply Charac4. left. assumption.
Qed.

(* Le is a well-ordering on On x On.                                            *)
Proposition IsWellOrdering : WellOrdering Le (On :x: On).
Proof.
  split.
  - apply IsFounded.
  - apply IsTotal.
Qed.

(* Le is not well-founded on On x On.                                           *)
Proposition IsNotWellFounded : ~ WellFounded Le (On :x: On).
Proof.
  intros [_ H1].
  assert ((On :x: On) :(:1:,:0:):) as H2. {
    apply Prod.Charac2. split.
    - apply Natural.OneIsOrdinal.
    - apply Natural.ZeroIsOrdinal. }
  specialize (H1 :(:1:,:0:): H2). clear H2.
  remember (fun x => exists a, On a /\ x = :(:0:,a):) as A eqn:H2.
  assert (forall y z, A :(y,z): <-> y = :0: /\ On z) as H3. {
    intros y z. split; intros H3.
    - rewrite H2 in H3. destruct H3 as [a [H3 H4]].
      apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H5]. subst.
      split. 2: assumption. reflexivity.
    - destruct H3 as [H3 H4]. subst. exists z.
      split. 1: assumption. reflexivity. }
  assert (A :~: initSegment Le (On :x: On) :(:1:,:0:):) as H4. {
    intros x. split; intros H4.
    - rewrite H2 in H4. destruct H4 as [a [H4 H5]].
      apply InitSegment.Charac. split.
      + subst. apply Prod.Charac2. split. 2: assumption.
        apply Natural.ZeroIsOrdinal.
      + subst. apply Charac4. left. apply Succ.IsIn.
    - apply InitSegment.Charac in H4. destruct H4 as [[a [b [H4 [H5 H6]]]] H7].
      subst. apply Charac4 in H7. destruct H7 as [H7|[H7 H8]].
      + rewrite Natural.OneExtension in H7. apply Single.Charac in H7. subst.
        exists b. split. 1: assumption. reflexivity.
      + apply SEM.Charac in H8. contradiction. }
  remember (fun x => exists a, On a /\ x = :(a,:(:0:,a):):) as F eqn:H5.
  assert (forall y z, F :(y,z): <-> On y /\ z = :(:0:,y):) as H6. {
    intros y z. split; intros H6.
    - rewrite H5 in H6. destruct H6 as [a [H6 H7]].
      apply OrdPair.WhenEqual in H7. destruct H7 as [H7 H8]. subst.
      split. 1: assumption. reflexivity.
    - destruct H6 as [H6 H7]. subst. exists y. split. 1: assumption. reflexivity. }
  assert (OneToOne F) as H7. {
    split.
    - intros x y z H7 H8. apply H6 in H7. apply H6 in H8.
      destruct H7 as [H7 H9]. destruct H8 as [H8 H10]. subst. reflexivity.
    - intros x y z H7 H8.
      apply Converse.Charac2 in H7. apply Converse.Charac2 in H8.
      apply H6 in H7. apply H6 in H8.
      destruct H7 as [H7 H9]. destruct H8 as [H8 H10]. rewrite H9 in H10.
      apply OrdPair.WhenEqual in H10. apply H10. }
  assert (domain F :~: On) as H8. {
    intros a. split; intros H8.
    - destruct H8 as [b H8]. apply H6 in H8. apply H8.
    - exists :(:0:,a):. apply H6. split. 1: assumption. reflexivity. }
  assert (range F :~: A) as H9. {
    intros b. split; intros H9.
    - destruct H9 as [a H9]. apply H6 in H9. destruct H9 as [H9 H10].
      rewrite H2. exists a. split; assumption.
    - rewrite H2 in H9. destruct H9 as [a [H9 H10]].
      exists a. apply H6. split; assumption. }
  assert (Small (range F)) as H10. {
    apply Small.EquivCompat with (initSegment Le (On :x: On) :(:1:,:0:):).
    2: assumption. apply Equiv.Tran with A; apply Equiv.Sym; assumption. }
  assert (Small On) as H11. {
    apply Small.EquivCompat with (domain F). 1: assumption.
    apply Function.DomainIsSmall; assumption. }
  revert H11. apply COC.OnIsProper.
Qed.



Require Import ZF.Axiom.Foundation.
Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Small.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Inter.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.

(* The class satisfied by all ordered pairs (x,y) with x :< y.                  *)
Definition E : Class := fun x => exists y z, x = :(y,z): /\ y :< z.

Proposition ECharac2 : forall (y z:U), E :(y,z): <-> y :< z.
Proof.
  intros y z. split; intros H1.
  - unfold E in H1. destruct H1 as [y' [z' [H1 H2]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst. assumption.
  - exists y. exists z. split. 1: reflexivity. assumption.
Qed.

Lemma InitSegmentEA : forall (A:Class) (a:U),
  initSegment E A a :~: A :/\: toClass a.
Proof.
  intros A a. split; intros [H1 H2].
  - apply InvImage.Charac in H2. destruct H2 as [y [H2 H3]].
    apply Single.Charac in H2. apply ECharac2 in H3.
    subst. split; assumption.
  - split. 1: assumption. apply InvImage.Charac. exists a. split.
    + apply Single.IsIn.
    + apply ECharac2. assumption.
Qed.

Lemma InitSegmentEV : forall (a:U),
  initSegment E V a :~: toClass a.
Proof.
  intros a. apply EquivTran with (V :/\: toClass a).
  - apply InitSegmentEA.
  - apply InterVL.
Qed.

Proposition MinimalEA : forall (A:Class) (a:U),
  Minimal E A a <-> A a /\ A :/\: toClass a :~: :0:.
Proof.
  intros A a. split; intros [H1 H2].
  - split. 1: assumption. apply EquivTran with (initSegment E A a).
    2: assumption. apply EquivSym, InitSegmentEA.
  - split. 1: assumption. apply EquivTran with (A :/\: toClass a).
    2: assumption. apply InitSegmentEA.
Qed.

(* The class E is founded on V, i.e. every subset of V has an E-minimal element.*)
Proposition EIsFoundedOnV : Founded E V.
Proof.
  (* Let a be an arbitrary set. *)
  intros a.

  (* We assume that a is non-empty. *)
  intros _ H1. assert (a <> :0:) as A. apply H1. clear A.

  (* We need to show that a has an E-minimal element. *)
  assert (exists x, Minimal E (toClass a) x) as A. 2: apply A.

  (* Applying the foundation axiom... *)
  apply Foundation in H1.

  (* We see that a has an element x such that x /\ a = 0. *)
  assert (exists x, x :< a /\ x :/\: a = :0:) as A. apply H1. clear A.

  (* So let x be such an element. *)
  destruct H1 as [x [H1 H2]].

  (* Then we have x :< a. *)
  assert (x :< a) as A. apply H1. clear A.

  (* And we have x /\ a = 0. *)
  assert (x :/\: a = :0:) as A. apply H2. clear A.

  (* We claim that such an x is our desired e-minimal element. *)
  exists x.

  (* So we need to show that x is E-minimal in a *)
  assert (Minimal E (toClass a) x) as A. 2: apply A.

  (* In other words... *)
  apply MinimalSuffice.

  (* We need to show that x :< a, which is true by assumption. *)
  - assert (x :< a) as A. 2: apply A. assumption.

  (* And given y in a *)
  - intros y H3. assert (y :< a) as A. apply H3. clear A.

  (* We need to show that E (y,x) does not hold. *)
    assert (~ E :(y,x):) as A. 2: apply A.

  (* So we assume to the contrary that E (y,x) is true. *)
    intros H4. assert (E :(y,x):) as A. apply H4. clear A.

  (* and we obtain a contradiction buy showing that y lies in x /\ a. *)
    apply Empty.Charac with y. rewrite <- H2.
    assert (y :< x :/\: a) as A. 2: apply A.

  (* Which follows easily. *)
    apply Inter.Charac. split. 2: assumption. apply ECharac2. assumption.
Qed.

Proposition EIsWellFoundedOnV : WellFounded E V.
Proof.
  split. 1: apply EIsFoundedOnV. intros a _.
  apply Small.EquivCompat with (toClass a).
  - apply EquivSym, InitSegmentEV.
  - apply SetIsSmall.
Qed.


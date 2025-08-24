Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Replacement.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.Image.
Export ZF.Notation.Image.

(* Direct image of a class Q by a class P.                                      *)
Definition image (F A:Class) : Class := fun y =>
  exists x, A x /\ F :(x,y):.

(* Notation "F :[ A ]:" := (image F A)                                          *)
Global Instance ClassImage : Image Class Class Class := { image := image }.

(* The direct image is compatible with equivalences.                            *)
Proposition EquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P:[R]: :~: Q:[S]:.
Proof.
  intros P Q R S H1 H2 y. split; intros H3;
  destruct H3 as [x [H3 H4]]; exists x; split.
  - apply H2. assumption.
  - apply H1. assumption.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.

(* The direct image is left-compatible with equivalences.                       *)
Proposition EquivCompatL : forall (P Q R:Class),
  P :~: Q -> P:[R]: :~: Q:[R]:.
Proof.
  intros P Q R H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

(* The direct image is right-compatible with equivalences.                      *)
Proposition EquivCompatR : forall (P Q R:Class),
  P :~: Q -> R:[P]: :~: R:[Q]:.
Proof.
  intros P Q R H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

(* The direct image is compatible with inclusion.                               *)
Proposition InclCompat : forall (P Q R S:Class),
  P :<=: Q -> R :<=: S -> P:[R]: :<=: Q:[S]:.
Proof.
  intros P Q R S H1 H2 y H3. destruct H3 as [x [H3 H4]].
  exists x. split.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.

(* The direct image is left-compatible with inclusion.                          *)
Proposition InclCompatL : forall (P Q R:Class),
  P :<=: Q -> P:[R]: :<=: Q:[R]:.
Proof.
  intros P Q R H1. apply InclCompat.
  - assumption.
  - apply Incl.Refl.
Qed.

(* The direct image is right-compatible with inclusion.                         *)
Proposition InclCompatR : forall (P Q R:Class),
  P :<=: Q -> R:[P]: :<=: R:[Q]:.
Proof.
  intros P Q R H1. apply InclCompat.
  - apply Incl.Refl.
  - assumption.
Qed.

(* If F is functional and P is small, then F:[P]: is small.                     *)
Proposition IsSmall : forall (F P:Class),
  Functional F -> Small P -> Small F:[P]:.
Proof.

  (* Let F and P be two arbitrary classes. *)
  intros F P.

  (* We assume that F is functional. *)
  intros H1. assert (Functional F) as A. { apply H1. } clear A.

  (* We assume that P is small. *)
  intros H2. assert (Small P) as A. { apply H2. } clear A.

  (* In particular P is equivalent to some set a. *)
  assert (exists a, toClass a :~: P) as H3. { assumption. }

  (* So let a be a set equivalent to the class P. *)
  destruct H3 as [a H3].

  (* We need to show that the direct image of P by F is small. *)
  assert (Small F:[P]:) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply Small.EquivCompat with F:[toClass a]:.

  (* We first need to show the equivalence between F[a] and F[P]. *)
  - assert (F:[toClass a]: :~: F:[P]:) as A. 2: apply A.

  (* Which follows from the equivalence between a and P. *)
    apply EquivCompatR, H3.

  (* We next need to show that F[a] is small. *)
  - assert (Small F:[toClass a]:) as A. 2: apply A.

  (* Which follows from replacement and the fact F is functional. *)
    apply Replacement, H1.
Qed.

(* If F is small, then F:[P]: is small.                                         *)
Proposition IsSmall' : forall (F P:Class),
    Small F -> Small F:[P]:.
Proof.
  (* Let F and P be two arbitrary classes. *)
  intros F P.

  (* We assume that F is small. *)
  intros H1. assert (Small F) as A. { apply H1. } clear A.

  (* We need to show that F[P] is small. *)
  assert (Small F:[P]:) as A. 2: apply A.

  (* Consider the function Snd : (y,z) -> z defined on PxV. *)
  remember (fun x => exists y z, x = :(:(y,z):,z): /\ P y) as Snd eqn:H2.

  (* We claim that Snd is a functional class. *)
  assert (Functional Snd) as H3. {
    intros x y z H3 H4.
    rewrite H2 in H3. destruct H3 as [y1 [z1 [H3 _]]].
    rewrite H2 in H4. destruct H4 as [y2 [z2 [H4 _]]].
    apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H5].
    apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H6].
    rewrite H3 in H4. apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H7].
    subst. reflexivity. }

  (* Having assumed F to be small, we have a set f. *)
  destruct H1 as [f H1].

  (* x :< f iff F x. *)
  assert (forall x, x :< f <-> F x) as A. { apply H1. } clear A.

  (* Applying the replacement theorem to f and Snd, we have a set a. *)
  assert (exists a, forall y, y :< a <-> exists x, x :< f /\ Snd :(x,y):) as H8. {
    apply Replacement. assumption. }

  destruct H8 as [a H8].

  (* y :< a iff exists x, x :< f /\ (x,y) in Snd. *)
  assert (forall y, y :< a <-> exists x, x :< f /\ Snd :(x,y):) as A.
    { apply H8. } clear A.

  (* We claim that the set a demonstrates that F[P] is small. *)
  exists a.

  (* So we need to show x :< a iff x in F[P]. *)
  assert (forall x, x :< a <-> F:[P]: x) as A. 2: apply A.

  intros z. split; intros H9.
  - apply H8 in H9. destruct H9 as [x [H9 H10]]. rewrite H2 in H10.
    destruct H10 as [y [z' [H10 H11]]]. apply OrdPair.WhenEqual in H10.
    destruct H10 as [H10 H12]. subst. apply H1 in H9.
    exists y. split; assumption.
  - destruct H9 as [y [H9 H10]]. apply H1 in H10. apply H8. exists :(y,z):.
    split. 1: assumption. rewrite H2. exists y. exists z. split.
    2: assumption. reflexivity.
Qed.

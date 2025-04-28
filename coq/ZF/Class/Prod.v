Require Import ZF.Class.Core.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Small.
Require Import ZF.Class.Relation.Switch.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Prod.
Export ZF.Notation.Prod.

(* The class of all ordered pairs (y,z) where y lies in P and z lies in Q.      *)
Definition prod (P Q:Class) : Class := fun x =>
  exists y, exists z, x = :(y,z): /\ P y /\ Q z.

(* Notation "P :x: Q" := (prod P Q)                                             *)
Global Instance ClassProd : Prod Class := { prod := prod }.

Proposition Charac2 : forall (P Q:Class) (y z:U),
  (P :x: Q) :(y,z): <-> P y /\ Q z.
Proof.
  intros P Q y z. split; intros H1.
  - unfold prod in H1. destruct H1 as [y' [z' [H1 [H2 H3]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H1'].
    subst. split; assumption.
  - destruct H1 as [H1 H2]. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

(* The product of two classes is compatible with class equivalence.             *)
Proposition EquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P :x: R :~: Q :x: S.
Proof.
  intros P Q R S H1 H2 x. split; intros H3;
  destruct H3 as [y [z [H3 [H4 H5]]]]; exists y; exists z;
  split; try assumption.
  - split. { apply H1. assumption. } { apply H2. assumption. }
  - split.
    + apply H1. assumption.
    + apply H2. assumption.
Qed.

(* The product of two classes is left-compatible with class equivalence.        *)
Proposition EquivCompatL : forall (P Q R:Class),
  P :~: Q -> P :x: R :~: Q :x: R.
Proof.
  intros P Q R H1. apply EquivCompat.
  - assumption.
  - apply EquivRefl.
Qed.

(* The product of two classes is right-compatible with class equivalence.       *)
Proposition EquivCompatR : forall (P Q R:Class),
  P :~: Q -> R :x: P :~: R :x: Q.
Proof.
  intros P Q R H1. apply EquivCompat.
  - apply EquivRefl.
  - assumption.
Qed.

(* The product of two classes is compatible with class inclusion.               *)
Proposition InclCompat : forall (P Q R S:Class),
  P :<=: Q -> R :<=: S -> P :x: R :<=: Q :x: S.
Proof.
  intros P Q R S H1 H2 x [y [z [H3 [H4 H5]]]].
  exists y. exists z. split. 1: assumption. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* The product of two classes is left-compatible with class inclusion.          *)
Proposition InclCompatL : forall (P Q R:Class),
  P :<=: Q -> P :x: R :<=: Q :x: R.
Proof.
  intros P Q R H1. apply InclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* The product of two classes is right-compatible with class inclusion.         *)
Proposition InclCompatR : forall (P Q R:Class),
  P :<=: Q -> R :x: P :<=: R :x: Q.
Proof.
  intros P Q R H1. apply InclCompat.
  - apply InclRefl.
  - assumption.
Qed.

(* The product of two small classes is a small class.                           *)
Proposition IsSmall : forall (P Q:Class),
  Small P -> Small Q -> Small (P :x: Q).
Proof.
  (* Let P and Q be arbitrary classes *)
  intros P Q.

  (* We assume that P is small *)
  intros H1. assert (Small P) as A. { apply H1. } clear A.

  (* Amd we assume that Q is small *)
  intros H2. assert (Small Q) as A. { apply H2. } clear A.

  (* P is equivalent to some set a. *)
  assert (exists a, P :~: toClass a) as H3. { apply Small.IsSomeSet, H1. }

  (* Q is equivalent to some set b. *)
  assert (exists b, Q :~: toClass b) as H4. { apply Small.IsSomeSet, H2. }

  (* So let a be a set equivalent to the class P. *)
  destruct H3 as [a H3].

  (* And let b be a set equivalent to the class Q. *)
  destruct H4 as [b H4].

  (* We need to show that the producr of P and Q is small. *)
  assert (Small (P :x: Q)) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply Small.EquivCompat with (toClass a :x: toClass b).

  (* We first need to show the equivalence between P \/ Q and a \/ b. *)
  - assert (toClass a :x: toClass b :~: P :x: Q) as A. 2: apply A.

  (* Which follows from the equivalences of a and P and  of b and Q. *)
    apply EquivCompat; apply EquivSym; assumption.

  (* We next need to show that a x b is small. *)
  - assert (Small (toClass a :x: toClass b)) as A. 2: apply A.

  (* It is sufficient to show that a x b is a bounded class. *)
    apply BoundedIsSmall.

  (* So we need to show that a x b is bounded. *)
    assert (Bounded (toClass a :x: toClass b)) as A. 2: apply A.

  (* In other words, we need to show the existence of a set c ... *)
    assert (exists c, forall x, (toClass a :x: toClass b) x -> x :< c) as A.
    2: apply A.

  (* Consider the set c = P(P(a\/b)) *)
    remember :P(:P(a:\/:b)) as c eqn:Ec.

  (* We claim that c has the desired property *)
    exists c.

  (* We need to show that (a x b) x -> x :< c for all x *)
    assert (forall x, (toClass a :x: toClass b) x -> x :< c) as A. 2: apply A.

  (* So let x be an arbitrary set satisfying the predicate a x b *)
    intros x H5.

  (* Then we have some y and z such that y :< a, z :< b and x = (y,z) *)
    destruct H5 as [y [z [H5 [H6 H7]]]].

  (* So x is the ordered pair (y,z) *)
    assert (x = :(y,z):) as A. { apply H5. } clear A.

  (* And  we have y :< a *)
    assert (y :< a) as A. { apply H6. } clear A.

  (* And we have z :< b *)
    assert (z :< b) as A. { apply H7. } clear A.

  (* So we need to show thar x :< c *)
    assert (x :< c) as A. 2: apply A.

  (* In other words, we need to show that x :< P(P(a\/b)) *)
    rewrite Ec.
    assert (x :< :P(:P(a:\/:b))) as A. 2: apply A.

  (* That is, we need to show that (y,z) <= P(a\/b) *)
    apply Power.Charac. rewrite H5.
    assert (:(y,z): :<=: :P(a:\/:b)) as A. 2: apply A.

  (* So let u be an element of (y,z) *)
    intros u H8. apply OrdPair.Charac in H8.

  (* Since (y,z) = {{y},{y,z}} we have u = {y} or u = {y,z} *)
    assert (u = :{y}: \/ u = :{y,z}: ) as A. { apply H8. } clear A.

  (* And we need to show that u is an element of P(a\/b) *)
    assert (u :< :P(a:\/:b)) as A. 2: apply A.

 (* That is, we need to show that u <= a\/b *)
    apply Power.Charac.
    assert (u :<=: a:\/:b) as A. 2: apply A.

 (* We consider the cases u = {y} and u = {y,z} separately *)
    destruct H8 as [H8|H8]; rewrite H8.

 (* case u = {y} : we need to show that {y} <= a\/b, given that y :< a *)
    + assert (:{y}: :<=: a:\/:b) as A. 2: apply A.
      intros v H9. apply Single.Charac in H9. apply Union2.Charac.
      subst. left. apply H6.

 (* case u = {y,z} : we need to show that {y,z} <= a\/b with y :< a and z :< b *)
    + assert (:{y,z}: :<=: a:\/:b) as A. 2: apply A.
      intros v H9. apply Pair.Charac in H9. apply Union2.Charac.
      destruct H9 as [H9|H9]; subst.
      * left.  apply H6.
      * right. apply H7.
Qed.

(* The direct image of P x Q by Switch is Q x P.                                *)
Lemma ImageBySwitch : forall (P Q:Class),
  Switch :[P :x: Q]: :~: Q :x: P.
Proof.
  intros P Q x'. split; intros H1.
  - destruct H1 as [x [H1 H2]]. destruct H1 as [y [z [H3 [H4 H5]]]].
    apply Switch.Charac2 in H2. destruct H2 as [y' [z' [H6 H7]]]. subst.
    apply OrdPair.WhenEqual in H6. destruct H6 as [H6 H8]. subst.
    exists z'. exists y'. split. 1: reflexivity. split; assumption.
  - destruct H1 as [z [y [H1 [H2 H3]]]]. exists :(y,z):. split.
    + apply Charac2. split; assumption.
    + apply Switch.Charac2. exists y. exists z. split.
      * reflexivity.
      * assumption.
Qed.

(* If P x Q is a small class, then so is Q x P.                                 *)
Proposition IsSmallComm : forall (P Q:Class),
  Small (P :x: Q) -> Small (Q :x: P).
Proof.

  (* Let P and Q be arbitrary classes. *)
  intros P Q.

  (* We assume that P x Q is small. *)
  intros H1. assert (Small (P :x: Q)) as A. { apply H1. } clear A.

  (* And we need to show that Q x P is small *)
  assert (Small (Q :x: P)) as A. 2: apply A.

  (* Using the equivalence Switch[P x Q] ~ Q x P ... *)
  apply Small.EquivCompat with Switch:[P :x: Q]:. 1: apply ImageBySwitch.

  (* It is sufficient to show that Switch[P x Q] is small. *)
  assert (Small (Switch:[P :x: Q]:)) as A. 2: apply A.

  (* This follows from the fact that Switch is functional and P x Q is small. *)
  apply Image.IsSmall.

  - apply Switch.IsFunctional.

  - apply H1.
Qed.

(* If P is a proper class and Q is not empty, then P x Q is a proper class.     *)
Proposition IsProper : forall (P Q:Class),
  Proper P -> ~ Q :~: :0: -> Proper (P :x: Q).
Proof.

  (* Let P and Q be two arbitrary classes. *)
  intros P Q.

  (* We assume that P is a proper class. *)
  intros H1. assert (Proper P) as A. { apply H1. } clear A.

  (* We assume that Q is not empty. *)
  intros H2. assert (~ Q :~: :0:) as A. { apply H2. } clear A.

  (* So Q has an element. *)
  assert (exists y, Q y) as H3. { apply NotEmptyHasElem, H2. }

  (* So let y be a set belonging to the class Q. *)
  destruct H3 as [y H3].

  (* We need to show that P x Q is a proper class. *)
  assert (Proper (P :x: Q)) as A. 2: apply A.

  (* Let us assume to the contrary that P X Q is small. *)
  intros H4. assert (Small (P :x: Q)) as A. { apply H4. } clear A.

  (* We shall obtain a contradiction by showing that P is small *)
  apply H1.

  (* So we need to show that P is small. *)
  assert (Small P) as A. 2: apply A.

  (* Consider the class R = { ((x,y),x) | P x }. *)
  remember ( fun z => exists x, z = :(:(x,y):,x): /\ P x) as R eqn:Er.

  (* We claim that R is a functional class *)
  assert (Functional R) as H5. {
    intros x y1 y2. rewrite Er.
    intros [x1 [T1 T2]] [x2 [T3 T4]].
    apply OrdPair.WhenEqual in T1. destruct T1 as [T1 T1'].
    apply OrdPair.WhenEqual in T3. destruct T3 as [T3 T3'].
    subst. apply OrdPair.WhenEqual in T3. destruct T3 as [T3 _].
    assumption.
  }

  (* We claim that domain R <= P X Q. *)
  assert (domain R :<=: P :x: Q) as H6. {
    intros x T1.
    destruct T1 as [y' T1]. rewrite Er in T1.
    destruct T1 as [x' [T1 T2]]. apply OrdPair.WhenEqual in T1.
    destruct T1 as [T1 _]. subst. apply Charac2. split; assumption.
  }

  (* Having assumed that P x Q is small, it follows that domain R is small. *)
  assert (Small (domain R)) as H7. {
    apply LesserThanSmallIsSmall with (P :x: Q); assumption.
  }

  (* However, we claim that P is the direct image of domain R by R. *)
  assert (R:[domain R]: :~: P) as H8. {
    intros x. split; intros T1.
    - destruct T1 as [x' [_ T1]].
      rewrite Er in T1. destruct T1 as [x1 [T1 T2]].
      apply OrdPair.WhenEqual in T1. destruct T1 as [_ T1]. subst. assumption.
    - exists :(x,y):. rewrite Er. split.
      + exists x. exists x. split. 1: reflexivity. assumption.
      + exists x. split. 1: reflexivity. assumption.
  }

  (* Using this equivalence ... *)
  apply Small.EquivCompat with R:[domain R]:. 1: apply H8.

  (* It is sufficient to show that R[domain R] is small. *)
  assert (Small R:[domain R]:) as A. 2: apply A.

  (* Which follows from the fact that R is functional and domain R is small. *)
  apply Image.IsSmall.
    - apply H5.
    - apply H7.
Qed.

(* If P is a proper class, then so is PxP.                                      *)
Proposition SquareIsProper : forall (P:Class),
  Proper P -> Proper (P :x: P).
Proof.

  (* Let P be an arbitrary class. *)
  intros P.

  (* We assume that P is proper. *)
  intros H1. assert (Proper P) as A. { apply H1. } clear A.

  (* And we need to show that P^2 is proper. *)
  assert (Proper (P :x: P)) as A. 2: apply A.

  (* This follows immediately from the fact that P is proper. *)
  apply IsProper. 1: apply H1.

  (* Provided we show P is not the empty class. *)
  assert (~ P :~: :0:) as A. 2: apply A.

  (* So let us assume that P is the empty class. *)
  intros H2. assert (P :~: :0:) as A. { apply H2. } clear A.

  (* We obtain a contradiction my showing that P is small. *)
  apply H1. assert (Small P) as A. 2: apply A.

  (* From the equivalence P ~ 0 *)
  apply Small.EquivCompat with :0:. 1: { apply EquivSym, H2. }

  (* We need to show that 0 is small *)
  assert (Small :0:) as A. 2: apply A.

  (* Which we know is true. *)
  apply Empty.IsSmall.

Qed.

Proposition InterProdIsProdInter: forall (P1 P2 Q1 Q2:Class),
  (P1:x:Q1) :/\: (P2:x:Q2) :~: (P1:/\:P2) :x: (Q1:/\:Q2).
Proof.
  intros P1 P2 Q1 Q2. apply DoubleInclusion. split; intros x H1.
  - destruct H1 as [H1 H2].
    destruct H1 as [y1 [z1 [G1 [H1 H1']]]].
    destruct H2 as [y2 [z2 [G2 [H2 H2']]]].
    subst. apply OrdPair.WhenEqual in G2. destruct G2 as [G1 G2]. subst.
    apply Charac2. split; split; assumption.
  - unfold prod in H1. destruct H1 as [y [z [H1 [[H2 H2'] [H3 H3']]]]].
    split; exists y; exists z; split.
    + apply H1.
    + split; assumption.
    + apply H1.
    + split; assumption.
Qed.


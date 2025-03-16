Require Import ZF.Class.
Require Import ZF.Class.Founded.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Irreflexive.
Require Import ZF.Class.Minimal.
Require Import ZF.Class.StrictOrd.
Require Import ZF.Class.StrictTotalOrd.
Require Import ZF.Class.Total.
Require Import ZF.Class.Transitive.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Tuple.

(* Predicate expressing the fact that R is a well-ordering class on A.          *)
(* R is a well-ordering on A iff it is founded on A and total on A.             *)
Definition WellOrdering (R A:Class) : Prop :=  Founded R A /\ Total R A.

Proposition WellOrderingIncl : forall (R A B:Class),
  WellOrdering R A -> B :<=: A -> WellOrdering R B.
Proof.
  intros R A B [H1 H2] H3. split.
  - apply FoundedIncl with A; assumption.
  - apply TotalIncl with A; assumption.
Qed.

Proposition WellOrderingIsIrreflexive : forall (R A:Class),
  WellOrdering R A -> Irreflexive R A.
Proof.
  intros R A [H1 H2] a H3.
  assert (exists x, Minimal R (toClass :{a}:) x) as H4. {
    apply H1.
    - apply SingleToClassIncl. assumption.
    - apply SingletonIsNotEmpty.
  } destruct H4 as [x H4]. assert (H5 := H4). apply MinimalIn in H5.
  apply SingleCharac in H5. subst.
  apply MinimalHasNoLesser with (toClass :{a}:). 2: assumption. apply SingleIn.
Qed.

Proposition WellOrderingIsTransitive : forall (R A:Class),
  WellOrdering R A -> Transitive R A.
Proof.
  intros R A [H1 H2] x y z H3 H4 H5 H6 H7.
  specialize (H2 x z H3 H5). destruct H2 as [H2|[H2|H2]].
  - subst. exfalso. assert (R :(y,z): /\ R :(z,y):) as H8. { split; assumption. }
    revert H8. apply (FoundedNoLoop2 R A H1 y z); assumption.
  - assumption.
  - exfalso. assert (exists u, Minimal R (toClass :{x,y,z}:) u) as H8. {
      apply H1.
      - apply Tuple3ToClassIncl. split. 1: assumption. split; assumption.
      - apply Tuple3IsNotEmpty.
    } destruct H8 as [u H8]. assert (H9 := H8). apply MinimalIn in H9.
    apply Tuple3Charac in H9. destruct H9 as [H9|[H9|H9]]; subst.
    + assert (~R :(z,x):) as H9. {
        apply MinimalHasNoLesser with (toClass :{x,y,z}:).
        2: assumption. apply Tuple3In3.
      } contradiction.

    + assert (~R :(x,y):) as H9. {
        apply MinimalHasNoLesser with (toClass :{x,y,z}:).
        2: assumption. apply Tuple3In1.
      } contradiction.

    + assert (~R :(y,z):) as H9. {
        apply MinimalHasNoLesser with (toClass :{x,y,z}:).
        2: assumption. apply Tuple3In2.
      } contradiction.
Qed.

Proposition WellOrderingIsStrictOrd : forall (R A:Class),
  WellOrdering R A -> StrictOrd R A.
Proof.
  intros R A H1. split.
  - apply WellOrderingIsIrreflexive. assumption.
  - apply WellOrderingIsTransitive. assumption.
Qed.

Proposition WellOrderingIsStrictTotalOrd :  forall (R A:Class),
  WellOrdering R A -> StrictTotalOrd R A.
Proof.
  intros R A H1. split.
  - apply WellOrderingIsStrictOrd. assumption.
  - apply H1.
Qed.

Proposition WellOrderingWhenLess : forall (R A:Class) (x y:U),
  A x                ->
  A y                ->
  WellOrdering R A   ->
  R :(x,y):         <->
  ~ (x = y \/ R :(y,x): ).
Proof.
  intros R A x y H1 H2 H3. apply StrictTotalOrdWhenLess with A.
  - assumption.
  - assumption.
  - apply WellOrderingIsStrictTotalOrd. assumption.
Qed.

(* If R well-orders A the minimal element of a subset of A is unique.           *)
Proposition WellOrderingHasUniqueMinimal : forall (R A:Class) (a x y:U),
  WellOrdering R A        ->
  toClass a :<=: A        ->
  Minimal R (toClass a) x ->
  Minimal R (toClass a) y ->
  x = y.
Proof.

  (* Let R A be arbitrary classes and a x y arbitrary sets. *)
  intros R A a x y.

  (* We assume that R is a well-ordering on A. *)
  intros H1. assert (WellOrdering R A) as X. apply H1. clear X.

  (* We assume that a is a subset of A. *)
  intros H2. assert (toClass a :<=: A) as X. apply H2. clear X.

  (* We assume that x is R-minimal in a. *)
  intros H4. assert (Minimal R (toClass a) x) as X. apply H4. clear X.

  (* And we assume that y is R-minimal in a. *)
  intros H5. assert (Minimal R (toClass a) y) as X. apply H5. clear X.

  (* We need to show that x = y. *)
  assert (x = y) as X. 2: apply X.

  (* Being a well-ordering on A, R is total on A. *)
  assert (Total R A) as H6. apply H1.

  (* x is also an element of A. *)
  assert (A x) as H7. { apply H2. apply MinimalIn with R. assumption. }

  (* And y is an element of A. *)
  assert (A y) as H8. { apply H2. apply MinimalIn with R. assumption. }

  (* From the totality of R on A we see that x = y \/  x R y \/ y R x. *)
  specialize (H6 x y H7 H8).
  assert (x = y \/ R :(x,y): \/ R :(y,x):) as X. apply H6. clear X.

  (* We consider these three cases separately. *)
  destruct H6 as [H6|[H6|H6]].

  (* We first consider the case when x = y. *)
  - assert (x = y) as X. apply H6. clear X.

    (* Then we are done. *)
    assumption.

  (* We then consider the case x R y. *)
  - assert (R :(x,y):) as X. apply H6. clear X.

  (* This contradicts the minimality of y. *)
    assert (~R :(x,y):) as H9. {
      apply (MinimalHasNoLesser _ (toClass a)). 2: assumption.
      apply (MinimalIn R). assumption.
    } contradiction.

  (* We finally consider the case y R x. *)
  - assert (R :(y,x):) as X. apply H6. clear X.

  (* This contradicts the minimality of x. *)
    assert (~R :(y,x):) as H9. {
      apply (MinimalHasNoLesser _ (toClass a)). 2: assumption.
      apply (MinimalIn R). assumption.
    } contradiction.
Qed.

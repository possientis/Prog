Require Import ZF.Class.
Require Import ZF.Class.Founded.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Minimal.
Require Import ZF.Class.Total.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a well-ordering class on A.          *)
(* R is a well-ordering on A iff it is founded on A and total on A.             *)
Definition WellOrdering (R A:Class) : Prop :=  Founded R A /\ Total R A.

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

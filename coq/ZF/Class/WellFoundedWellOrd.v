Require Import ZF.Axiom.Classic.
Require Import ZF.Class.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.InitSegment.
Require Import ZF.Class.Minimal.
Require Import ZF.Class.Small.
Require Import ZF.Class.WellFounded.
Require Import ZF.Class.WellOrdering.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

(* Predicate expressing the fact that R is a well-founded well-ordering on A.   *)
Definition WellFoundedWellOrd (R A:Class) : Prop :=
  WellFounded R A /\ WellOrdering R A.

(* If R is a wfwo on A, every non-empty subclass of A has an R-minimal element. *)
Proposition WellFoundedWellOrdHasMinimal : forall (R A B:Class),
  WellFoundedWellOrd R A ->
   B :<=: A              ->
  ~B :~: :0:             ->
  exists x, Minimal R B x.
Proof.

  (* Let R A B be arbitrary classes. *)
  intros R A B.

  (* We assume that R is a well-founded well-ordering on A. *)
  intros [H1 H2].

  (* In perticular, R is well-founded on A. *)
  assert (WellFounded R A) as X. apply H1. clear X.

  (* And R is a well-ordering on A. *)
  assert (WellOrdering R A) as X. apply H2. clear X.

  (* We assume that B is a subclass of A. *)
  intros H3. assert (B :<=: A) as X. apply H3. clear X.

  (* We assume that B is a non-empty class. *)
  intros H4. assert (~ B :~: :0:) as X. apply H4. clear X.

  (* We need to show that B has an R-minimal element. *)
  assert (exists x, Minimal R B x) as X. 2: apply X.

  (* Being non-empty, B has an element, *)
  apply NotEmptyHasElement in H4.

  (* Let b be such an element of B. *)
  destruct H4 as [b H4]. assert (B b) as X. apply H4. clear X.

  (* Let C be the initital segment of R in B at b. *)
  remember (initSegment R B b) as C eqn:EC.

  (* Either C is an empty class or it is not. *)
  assert (C :~: :0: \/ ~ C :~: :0:) as H5. apply LawExcludedMiddle.

  (* We shall consider these two cases separately. *)
  destruct H5 as [H5|H5].

  (* We first assume that C is empty. *)
  - assert (C :~: :0:) as X. apply H5. clear X.

  (* We claim that b is our desired minimal element. *)
    exists b.

  (* So we need to prove that b in R-minimal in B. *)
    assert (Minimal R B b) as X. 2: apply X. split.

  (* Which follows from the fact that b lies in B. *)
    + assert (B b) as X. 2: apply X. assumption.

  (* And that the initial segment at b in B is empty. *)
    + assert (initSegment R B b :~: :0:) as X. 2: apply X.
      rewrite <- EC. assumption.

  (* So we now assume that C is an non-empty class. *)
  - assert (~ C :~: :0:) as X. apply H5. clear X.

  (* R being well-founded on A, it is well-founded on B. *)
    assert (WellFounded R B) as H6. { apply WellFoundedIncl with A; assumption. }

  (* And furthermore C is a small class. *)
    assert (Small C) as H7. { rewrite EC. apply H6. assumption. }

  (* Let c be the set defined by the class C. *)
    remember (fromClass C H7) as c eqn:Ec.

  (* Then we have toClass c = C. *)
    assert (toClass c :~: C) as H8. { rewrite Ec. apply ToFromClass. }

  (* Furthermore, the set c is not empty. *)
    assert (c <> :0:) as H9. { Admitted.

